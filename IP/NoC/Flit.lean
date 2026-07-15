/-
  NoC — Flit and Packet Types (pure Lean spec)

  A *packet* is what a tile wants to send.  It is chopped into *flits*
  (flow-control units): the chunk that crosses one link in one cycle.

      packet:  [ HEAD ][ BODY ][ BODY ][ TAIL ]
                  |                       |
            dest = (x,y)            "last flit"

  Only the HEAD carries a destination — the router computes a route from
  it and *reserves* the chosen output port.  BODY/TAIL flits carry no
  address; they follow the head through the reserved port (wormhole
  switching), and TAIL releases the reservation.

  This file is pure spec: no Signal DSL, no hardware.  The hardware
  encoding (`toBits`) is here so that `Router.lean` and the proofs agree
  on one representation.
-/

import Std.Tactic.BVDecide

namespace Sparkle.IP.NoC

/-- A router port.  `Local` is the tile (CPU / accelerator) attached to
    this router; the other four are the mesh neighbours. -/
inductive Port where
  | North | South | East | West | Local
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Position of a router in the 2-D mesh. -/
structure Coord where
  x : Nat
  y : Nat
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Position of a flit within its packet (the "worm"). -/
inductive FlitKind where
  | Head | Body | Tail
  deriving DecidableEq, Repr, BEq, Inhabited

/-- One flit: the unit that crosses a link in a single cycle. -/
structure Flit where
  kind    : FlitKind
  /-- Destination.  Only meaningful when `kind = Head`. -/
  dest    : Coord
  payload : BitVec 32
  deriving DecidableEq, Repr, BEq, Inhabited

/-! ## Hardware encoding

    These fix the bit-level representation shared by the RTL and the
    proofs.  4 bits of coordinate per axis ⇒ meshes up to 16×16. -/

/-- 3-bit port encoding used by the crossbar select lines. -/
def Port.toBits : Port → BitVec 3
  | .North => 0#3
  | .South => 1#3
  | .East  => 2#3
  | .West  => 3#3
  | .Local => 4#3

/-- 2-bit flit-kind encoding. -/
def FlitKind.toBits : FlitKind → BitVec 2
  | .Head => 0#2
  | .Body => 1#2
  | .Tail => 2#2

/-- Wire format of a flit:

        [41:40] kind   (Head / Body / Tail)
        [39:36] dest.x (4 bits ⇒ meshes up to 16 wide)
        [35:32] dest.y
        [31: 0] payload

    42 bits crossing each link per cycle. -/
def flitWidth : Nat := 42

/-- A flit as it appears on the wire. -/
abbrev FlitBits := BitVec 42

/-- **The wire encoding — the single definition of the flit layout.**
    The field extractors below are the only other place that mentions
    bit positions, and the round-trip theorems pin them to this
    packing.  `Router.lean` (hardware) and `SimTest.lean` (testbench)
    both consume these; neither re-states the layout. -/
def Flit.toBits (f : Flit) : FlitBits :=
  f.kind.toBits ++ BitVec.ofNat 4 f.dest.x ++ BitVec.ofNat 4 f.dest.y ++ f.payload

/-! ## Field extraction, and proof that it inverts the packing -/

-- `bv_decide`'s bit-blasting of the 42-bit concatenation needs more
-- recursion headroom than the default.
set_option maxRecDepth 2048

def kindBits    (b : FlitBits) : BitVec 2  := BitVec.extractLsb' 40 2 b
def destXBits   (b : FlitBits) : BitVec 4  := BitVec.extractLsb' 36 4 b
def destYBits   (b : FlitBits) : BitVec 4  := BitVec.extractLsb' 32 4 b
def payloadBits (b : FlitBits) : BitVec 32 := BitVec.extractLsb' 0 32 b

-- The four extraction-inverts-concatenation facts, over pure bitvector
-- variables so `bv_decide` can bit-blast them directly.
private theorem extract_kind (a : BitVec 2) (b c : BitVec 4) (d : BitVec 32) :
    BitVec.extractLsb' 40 2 (a ++ b ++ c ++ d) = a := by bv_decide

private theorem extract_destX (a : BitVec 2) (b c : BitVec 4) (d : BitVec 32) :
    BitVec.extractLsb' 36 4 (a ++ b ++ c ++ d) = b := by bv_decide

private theorem extract_destY (a : BitVec 2) (b c : BitVec 4) (d : BitVec 32) :
    BitVec.extractLsb' 32 4 (a ++ b ++ c ++ d) = c := by bv_decide

private theorem extract_payload (a : BitVec 2) (b c : BitVec 4) (d : BitVec 32) :
    BitVec.extractLsb' 0 32 (a ++ b ++ c ++ d) = d := by bv_decide

/-! The extractors invert the packing — so any two readers of the wire
    that go through `kindBits`/`destXBits`/`destYBits`/`payloadBits`
    agree with any writer that goes through `Flit.toBits`. -/

theorem kindBits_toBits (f : Flit) : kindBits f.toBits = f.kind.toBits :=
  extract_kind ..

theorem destXBits_toBits (f : Flit) : destXBits f.toBits = BitVec.ofNat 4 f.dest.x :=
  extract_destX ..

theorem destYBits_toBits (f : Flit) : destYBits f.toBits = BitVec.ofNat 4 f.dest.y :=
  extract_destY ..

theorem payloadBits_toBits (f : Flit) : payloadBits f.toBits = f.payload :=
  extract_payload ..

/-- Number of ports on a router (N/S/E/W + Local). -/
def numPorts : Nat := 5

/-- All ports, in a fixed order.  The index into this list is the port's
    channel number in the arbiter and crossbar. -/
def allPorts : List Port := [.North, .South, .East, .West, .Local]

end Sparkle.IP.NoC
