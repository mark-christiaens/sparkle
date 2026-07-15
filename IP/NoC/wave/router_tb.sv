// Waveform testbench for the Sparkle NoC wormhole router.
//
// Reproduces the scenario from `checkWormhole` in SimTest.lean: a router
// at (1,1) with two 5-flit packets injected at the same instant, from
// input North and input South, both addressed to (3,1) — so XY routing
// sends both to the East output and they must contend for it.
//
// What to look for in the waveform:
//   * `outV2` / `eastKind` / `eastPayload` — the East output: one
//     packet's five flits emerge back-to-back (Head,Body,Body,Body,Tail),
//     THEN the other's.  No interleaving.  That is wormhole switching,
//     and it is the whole point.
//   * `inR0` / `inR1` — backpressure: the loser's ready line is held low
//     for the five cycles the winner owns the East port, so its source
//     (`idxA`/`idxB`) stalls in place rather than corrupting the worm.
//   * `dut._gen_a0` / `dut._gen_t0` — the mechanism itself: input 0's
//     reservation flag and the output port it reserved.  Only present in
//     `--internals` (Icarus) mode; Verilator optimises them away.
//
// Build + run + view:  IP/NoC/wave/run.sh [--internals] [--view]

`timescale 1ns/1ps

module router_tb;

  // ── flit layout (single-sourced in IP/NoC/Flit.lean: Flit.toBits) ──
  //   [41:40] kind   0=Head 1=Body 2=Tail
  //   [39:36] dest.x
  //   [35:32] dest.y
  //   [31: 0] payload
  function automatic logic [41:0] mk_flit
      (input logic [1:0] kind, input logic [3:0] dx, dy, input logic [31:0] payload);
    mk_flit = {kind, dx, dy, payload};
  endfunction

  // Kind of flit `i` of an n-flit packet: Head, Body…, Tail.
  function automatic logic [1:0] kind_at (input int i, n);
    kind_at = (i == 0) ? 2'd0 : (i == n - 1) ? 2'd2 : 2'd1;
  endfunction

  localparam int PKT_LEN = 5;
  localparam int CYCLES  = 24;

  logic clk = 0;
  logic rst = 1;
  always #5 clk = ~clk;          // 100 MHz

  // ── packet sources ────────────────────────────────────────────────
  // A on input 0 (North), B on input 1 (South); both → (3,1) ⇒ East.
  int  idxA = 0, idxB = 0;
  wire vA = (idxA < PKT_LEN);
  wire vB = (idxB < PKT_LEN);
  wire [41:0] fA = mk_flit(kind_at(idxA, PKT_LEN), 4'd3, 4'd1, 32'hA0 + idxA);
  wire [41:0] fB = mk_flit(kind_at(idxB, PKT_LEN), 4'd3, 4'd1, 32'hB0 + idxB);

  // ── DUT ───────────────────────────────────────────────────────────
  logic [219:0] out;

  Sparkle_IP_NoC_router5 dut (
    .clk(clk), .rst(rst),
    ._gen_myX(4'd1), ._gen_myY(4'd1),
    ._gen_inV0(vA),  ._gen_inV1(vB),
    ._gen_inV2(1'b0), ._gen_inV3(1'b0), ._gen_inV4(1'b0),
    ._gen_inF0(fA),  ._gen_inF1(fB),
    ._gen_inF2(42'd0), ._gen_inF3(42'd0), ._gen_inF4(42'd0),
    ._gen_outR0(1'b1), ._gen_outR1(1'b1), ._gen_outR2(1'b1),   // downstream
    ._gen_outR3(1'b1), ._gen_outR4(1'b1),                      // always ready
    .out(out)
  );

  // ── unpack RouterOut (declare_signal_state packs MSB-first, in
  //    declaration order: oV0..oV4, oF0..oF4, iR0..iR4) ──────────────
  wire        outV [0:4];
  wire [41:0] outF [0:4];
  wire        inR  [0:4];
  generate
    for (genvar p = 0; p < 5; p++) begin : g_unpack
      assign outV[p] = out[219 - p];
      assign outF[p] = out[173 - 42*p +: 42];
      assign inR[p]  = out[4 - p];
    end
  endgenerate

  // Named aliases so the waveform is readable (East = port 2).
  wire        outV2 = outV[2];
  wire [41:0] outF2 = outF[2];
  wire [1:0]  eastKind    = outF2[41:40];
  wire [31:0] eastPayload = outF2[31:0];
  wire        inR0 = inR[0];
  wire        inR1 = inR[1];

  // ── injection side: the flits as they ENTER the router ────────────
  // The raw 42-bit fA/fB are unreadable in a waveform, so decode them
  // the same way `eastKind`/`eastPayload` decode the output.  `dest`
  // is carried by every flit on the wire but is only *meaningful* on a
  // head — the body/tail values are don't-care (see Flit.lean).
  wire [1:0]  aKind    = fA[41:40];
  wire [3:0]  aDestX   = fA[39:36];
  wire [3:0]  aDestY   = fA[35:32];
  wire [31:0] aPayload = fA[31:0];
  wire [1:0]  bKind    = fB[41:40];
  wire [3:0]  bDestX   = fB[39:36];
  wire [3:0]  bDestY   = fB[35:32];
  wire [31:0] bPayload = fB[31:0];

  // A flit actually crosses into the router on the cycle where it is
  // offered AND the router is ready — this is the handshake firing.
  wire acceptA = vA && inR0;
  wire acceptB = vB && inR1;

  // ── drive ─────────────────────────────────────────────────────────
  //
  // Everything happens on the NEGEDGE: the DUT's registers update on the
  // posedge, so mid-cycle is the one point where the combinational
  // outputs (outV/outF/inR) have settled and can be sampled without
  // racing the clock edge.  Sampling on the posedge instead reads a mix
  // of pre- and post-edge values, and the packets appear to interleave —
  // a testbench artefact, not a DUT bug.
  int n_east = 0;
  logic [1:0]  seen_kind [0:2*PKT_LEN-1];
  logic [31:0] seen_pay  [0:2*PKT_LEN-1];

  initial begin
    $dumpfile("IP/NoC/wave/router.vcd");
    $dumpvars(0, router_tb);

    @(negedge clk); rst = 0;     // one cycle of reset, then go

    for (int t = 0; t < CYCLES; t++) begin
      @(negedge clk);
      if (acceptA)
        $display("  cycle %0d: IN  North  kind=%0d dest=(%0d,%0d) payload=0x%0h",
                 t, aKind, aDestX, aDestY, aPayload);
      if (acceptB)
        $display("  cycle %0d: IN  South  kind=%0d dest=(%0d,%0d) payload=0x%0h",
                 t, bKind, bDestX, bDestY, bPayload);
      if (outV2) begin
        $display("  cycle %0d: OUT East   kind=%0d payload=0x%0h", t, eastKind, eastPayload);
        if (n_east < 2*PKT_LEN) begin
          seen_kind[n_east] = eastKind;
          seen_pay[n_east]  = eastPayload;
        end
        n_east = n_east + 1;
      end
      // A flit is consumed exactly when it is offered and the router is
      // ready — the same handshake the Lean testbench uses.
      if (acceptA) idxA = idxA + 1;
      if (acceptB) idxB = idxB + 1;
    end

    check_wormhole();
    $finish;
  end

  // The wormhole property, checked — not asserted.  The East port must
  // carry one packet's flits as an unbroken Head,Body…,Tail run, then
  // the other's.  Any interleaving fails here.
  task automatic check_wormhole;
    bit ok = 1;
    logic [31:0] base0, base1;
    if (n_east != 2*PKT_LEN) begin
      $display("\nFAIL: expected %0d flits on East, saw %0d", 2*PKT_LEN, n_east);
      ok = 0;
    end else begin
      base0 = seen_pay[0];
      base1 = seen_pay[PKT_LEN];
      // The two runs must start at the two packet tags, in either order.
      if (!((base0 == 32'hA0 && base1 == 32'hB0) ||
            (base0 == 32'hB0 && base1 == 32'hA0))) begin
        $display("\nFAIL: runs start at 0x%0h and 0x%0h, expected 0xa0 / 0xb0", base0, base1);
        ok = 0;
      end
      for (int i = 0; i < PKT_LEN; i++) begin
        if (seen_kind[i] !== kind_at(i, PKT_LEN) || seen_pay[i] !== base0 + i) ok = 0;
        if (seen_kind[PKT_LEN+i] !== kind_at(i, PKT_LEN) || seen_pay[PKT_LEN+i] !== base1 + i) ok = 0;
      end
      if (!ok) $display("\nFAIL: the two packets interleaved on the East port");
    end
    if (ok)
      $display("\nPASS: each packet crossed East as one unbroken run (0x%0h.. then 0x%0h..) - no interleaving.",
               base0, base1);
    else
      $fatal(1, "wormhole check failed");
  endtask

endmodule
