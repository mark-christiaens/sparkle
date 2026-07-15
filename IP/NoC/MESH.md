# NoC mesh & router topology

These diagrams match the RTL in `IP/NoC/` — the 5-port order (`Flit.allPorts`),
the XY routing rule (`Route.routeXY`), and the coordinate convention
(`North = +y`, `East = +x`).

## One router (5 ports)

Five valid/ready streams of 42-bit flits. `myX`/`myY` are wired-in inputs, so a
single Verilog module tiles the whole mesh.

```
                    North (+y)
                 in ↓        ↑ out
              ┌───────────────────┐
              │                   │
   West   in →│    Router         │→ out   East
   (−x)   out ←│   (myX, myY)     │← in    (+x)
              │                   │
              │   XY route +      │
              │   5×5 crossbar +  │
              │   per-out RR arb  │
              └───────────────────┘
                 in ↓        ↑ out
                    South (−y)

        Local (port 4): tile / CPU / accelerator
        in  = injection   out = ejection

   Port index order (allPorts):
   0=North  1=South  2=East  3=West  4=Local
```

## The mesh (routers tile edge-to-edge, no glue)

Each router's East out → its neighbor's West in, and North out → the neighbor
above's South in. Every node also hangs a tile off its Local port.

```
        y
        ▲   (North = +y)
        │
   (0,2)┼──────(1,2)──────(2,2)
        │ R ══════ R ══════ R
        │ ║        ║        ║          ══  bidirectional
        │ ║        ║        ║              link (2 channels)
   (0,1)┼ R ══════ R ══════ R
        │ ║        ║        ║           R  router + its tile
        │ ║        ║        ║              (Local port)
   (0,0)┼ R ══════ R ══════ R
        │
        └────────────────────────▶ x   (East = +x)
      (0,0)    (1,0)    (2,0)
```

## XY (dimension-order) routing — why it can't deadlock

A packet travels in **X first** (East/West) until its column matches the
destination, **then in Y** (North/South) until it arrives, then ejects Local.
The Y→X turn is forbidden — that's the turn that would close a cycle in the
"who-waits-for-whom" graph, and forbidding it is what `RouteProps.lean` /
`Deadlock.lean` prove.

Example: packet at `(0,0)` headed for `(2,1)` — go East, East, then North:

```
   (0,2)   (1,2)   (2,2)
     R       R       R

   (0,1)   (1,1)   (2,1)  ← dest, eject Local
     R       R       R↑
                     │ North (Y phase)
   (0,0)   (1,0)   (2,0)
     R──────R──────R
      East    East        (X phase first)
   src
```

At each hop the router compares `dest` to its own `(myX,myY)`:
`dest.x > myX → East`, `< → West`, else `dest.y > myY → North`,
`< → South`, else `Local` (arrived). Delivery takes exactly `dist(src,dest)`
hops — the Manhattan distance.

## Caveat

Outputs are currently **combinational** (see `Router.lean`), so a mesh has a
combinational path threading every router and Fmax drops as it grows. The
registered/skid-buffer output stage is the honest next step.
