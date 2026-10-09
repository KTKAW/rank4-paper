import QuiverProofs.LStarSyntax
namespace QuiverProofs.BoundedLStarData
open LStar

def q013Row0 : CoreRow 9 0 where
  quiver := ⟨-2,-2,-2,-2,1,-2⟩
  word := []
  edges k := match k.val with
    | 0 => .core 0 ⟨5,true⟩
    | 1 => .core 1 ⟨0,false⟩
    | 2 => .boundary { kind := .fork, quiver := ⟨-2,2,-6,2,-3,2⟩, returnVertex := 2 }
    | _ => .core 2 ⟨0,false⟩

def q013Row1 : CoreRow 9 0 where
  quiver := ⟨2,-6,-2,2,-1,0⟩
  word := [1]
  edges k := match k.val with
    | 0 => .boundary { kind := .diamond 2 3, quiver := ⟨-2,6,2,-10,-5,0⟩, returnVertex := 0 }
    | 1 => .core 0 ⟨0,false⟩
    | 2 => .core 3 ⟨0,false⟩
    | _ => .core 4 ⟨0,false⟩

def q013Row2 : CoreRow 9 0 where
  quiver := ⟨-4,-2,2,0,-1,2⟩
  word := [3]
  edges k := match k.val with
    | 0 => .boundary { kind := .diamond 1 2, quiver := ⟨4,2,-2,0,7,6⟩, returnVertex := 0 }
    | 1 => .core 5 ⟨0,false⟩
    | 2 => .core 5 ⟨0,true⟩
    | _ => .core 0 ⟨0,false⟩

def q013Row3 : CoreRow 9 0 where
  quiver := ⟨-10,6,-2,-2,-1,0⟩
  word := [1,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 3, quiver := ⟨10,-6,2,58,-1,-12⟩, returnVertex := 0 }
    | 1 => .core 6 ⟨0,false⟩
    | 2 => .core 1 ⟨0,false⟩
    | _ => .core 7 ⟨0,false⟩

def q013Row4 : CoreRow 9 0 where
  quiver := ⟨2,-6,2,2,1,0⟩
  word := [1,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 3, quiver := ⟨-2,6,-2,-10,1,12⟩, returnVertex := 0 }
    | 1 => .core 5 ⟨5,false⟩
    | 2 => .core 7 ⟨0,false⟩
    | _ => .core 1 ⟨0,false⟩

def q013Row5 : CoreRow 9 0 where
  quiver := ⟨4,-2,-2,0,1,2⟩
  word := [3,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨-4,2,2,-8,-7,2⟩, returnVertex := 0 }
    | 1 => .core 2 ⟨0,false⟩
    | 2 => .core 2 ⟨0,true⟩
    | _ => .core 4 ⟨5,false⟩

def q013Row6 : CoreRow 9 0 where
  quiver := ⟨10,-14,-12,2,1,0⟩
  word := [1,2,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .diamond 2 3, quiver := ⟨-10,14,12,-138,-119,0⟩, returnVertex := 0 }
    | 1 => .core 3 ⟨0,false⟩
    | 2 => .zero (2) (12) (14) (18) { phase := 0, returnVertex := 2, frame := ⟨22,true⟩, alternateTarget := 8, alternateFrame := ⟨0,false⟩ }
    | _ => .core 8 ⟨0,false⟩

def q013Row7 : CoreRow 9 0 where
  quiver := ⟨-10,6,2,-2,1,0⟩
  word := [1,2,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .diamond 2 3, quiver := ⟨10,-6,-2,58,21,0⟩, returnVertex := 0 }
    | 1 => .core 9 ⟨0,false⟩
    | 2 => .core 4 ⟨0,false⟩
    | _ => .core 3 ⟨0,false⟩

def q013Row8 : CoreRow 9 0 where
  quiver := ⟨-2,-14,12,2,-1,0⟩
  word := [1,2,1,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨2,14,-12,2,23,168⟩, returnVertex := 0 }
    | 1 => .core 9 ⟨5,false⟩
    | 2 => .zero (2) (12) (14) (18) { phase := 1, returnVertex := 2, frame := ⟨22,true⟩, alternateTarget := 6, alternateFrame := ⟨0,false⟩ }
    | _ => .core 6 ⟨0,false⟩

def q013Row9 : CoreRow 9 0 where
  quiver := ⟨10,-14,2,2,-1,2⟩
  word := [1,2,3,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 3, quiver := ⟨-10,14,-2,-138,-1,30⟩, returnVertex := 0 }
    | 1 => .core 7 ⟨0,false⟩
    | 2 => .boundary { kind := .fork, quiver := ⟨-18,14,2,-2,3,-2⟩, returnVertex := 2 }
    | _ => .core 8 ⟨5,false⟩

def q013 : Certificate where
  initial := ⟨-2,-2,-2,-2,1,-2⟩
  entryWord := []
  entryFrame := ⟨0,false⟩
  size := 9
  stripCount := 0
  core i := match i.val with
    | 0 => q013Row0
    | 1 => q013Row1
    | 2 => q013Row2
    | 3 => q013Row3
    | 4 => q013Row4
    | 5 => q013Row5
    | 6 => q013Row6
    | 7 => q013Row7
    | 8 => q013Row8
    | _ => q013Row9
  strips := Fin.elim0
  triangleAvoidance := true

def q066Strip0 : StripRecord 25 where
  m := (2)
  a := (15)
  b := (6)
  c := (8)
  rootCore := 21
  rootQuiver := ⟨-2,-1,15,1,-8,6⟩
  rootWord := [2,3,0,2,1]
  rootFrame := ⟨2,false⟩
  backward p := match p.val with
    | 0 => ⟨20,⟨0,false⟩⟩
    | 1 => ⟨16,⟨2,false⟩⟩
    | _ => ⟨24,⟨6,false⟩⟩

def q066Strip1 : StripRecord 25 where
  m := (2)
  a := (46)
  b := (10)
  c := (21)
  rootCore := 22
  rootQuiver := ⟨1,-46,2,-10,1,-21⟩
  rootWord := [1,0,3,1,0,3]
  rootFrame := ⟨1,true⟩
  backward p := match p.val with
    | 0 => ⟨23,⟨7,false⟩⟩
    | 1 => ⟨18,⟨1,true⟩⟩
    | _ => ⟨25,⟨1,true⟩⟩

def q066Row0 : CoreRow 25 2 where
  quiver := ⟨-2,-2,-1,-1,1,-1⟩
  word := []
  edges k := match k.val with
    | 0 => .core 0 ⟨2,true⟩
    | 1 => .core 1 ⟨0,false⟩
    | 2 => .core 2 ⟨0,false⟩
    | _ => .core 3 ⟨0,false⟩

def q066Row1 : CoreRow 25 2 where
  quiver := ⟨2,-4,-1,1,-1,0⟩
  word := [1]
  edges k := match k.val with
    | 0 => .core 4 ⟨0,false⟩
    | 1 => .core 0 ⟨0,false⟩
    | 2 => .core 5 ⟨0,false⟩
    | _ => .core 5 ⟨0,true⟩

def q066Row2 : CoreRow 25 2 where
  quiver := ⟨-2,2,-3,1,0,1⟩
  word := [2]
  edges k := match k.val with
    | 0 => .boundary { kind := .diamond 1 3, quiver := ⟨2,-2,3,5,0,-5⟩, returnVertex := 0 }
    | 1 => .core 6 ⟨0,false⟩
    | 2 => .core 0 ⟨0,false⟩
    | _ => .core 7 ⟨0,false⟩

def q066Row3 : CoreRow 25 2 where
  quiver := ⟨-3,-2,1,0,-1,1⟩
  word := [3]
  edges k := match k.val with
    | 0 => .core 8 ⟨0,false⟩
    | 1 => .core 6 ⟨3,true⟩
    | 2 => .core 7 ⟨3,true⟩
    | _ => .core 0 ⟨0,false⟩

def q066Row4 : CoreRow 25 2 where
  quiver := ⟨-2,4,1,-7,-3,0⟩
  word := [1,0]
  edges k := match k.val with
    | 0 => .core 1 ⟨0,false⟩
    | 1 => .boundary { kind := .diamond 2 3, quiver := ⟨2,-10,-5,7,3,0⟩, returnVertex := 1 }
    | 2 => .zero (4) (3) (7) (26) { phase := 0, returnVertex := 2, frame := ⟨23,true⟩, alternateTarget := 9, alternateFrame := ⟨0,false⟩ }
    | _ => .core 9 ⟨0,false⟩

def q066Row5 : CoreRow 25 2 where
  quiver := ⟨-2,4,-1,-1,-1,0⟩
  word := [1,2]
  edges k := match k.val with
    | 0 => .core 10 ⟨0,false⟩
    | 1 => .core 6 ⟨2,false⟩
    | 2 => .core 1 ⟨0,false⟩
    | _ => .core 1 ⟨0,true⟩

def q066Row6 : CoreRow 25 2 where
  quiver := ⟨2,2,-3,-1,0,1⟩
  word := [2,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 2, quiver := ⟨-2,-2,3,-1,-6,-5⟩, returnVertex := 0 }
    | 1 => .core 2 ⟨0,false⟩
    | 2 => .core 5 ⟨2,false⟩
    | _ => .core 3 ⟨4,true⟩

def q066Row7 : CoreRow 25 2 where
  quiver := ⟨-2,-1,3,1,0,-1⟩
  word := [2,3]
  edges k := match k.val with
    | 0 => .core 11 ⟨0,false⟩
    | 1 => .core 3 ⟨4,true⟩
    | 2 => .core 7 ⟨5,true⟩
    | _ => .core 2 ⟨0,false⟩

def q066Row8 : CoreRow 25 2 where
  quiver := ⟨3,2,-1,0,2,3⟩
  word := [3,0]
  edges k := match k.val with
    | 0 => .core 3 ⟨0,false⟩
    | 1 => .core 12 ⟨0,false⟩
    | 2 => .core 12 ⟨23,true⟩
    | _ => .core 3 ⟨23,true⟩

def q066Row9 : CoreRow 25 2 where
  quiver := ⟨1,4,-1,-7,3,0⟩
  word := [1,0,3]
  edges k := match k.val with
    | 0 => .core 10 ⟨21,true⟩
    | 1 => .core 13 ⟨0,false⟩
    | 2 => .zero (4) (3) (7) (26) { phase := 1, returnVertex := 2, frame := ⟨23,true⟩, alternateTarget := 4, alternateFrame := ⟨0,false⟩ }
    | _ => .core 4 ⟨0,false⟩

def q066Row10 : CoreRow 25 2 where
  quiver := ⟨2,-4,1,7,-1,-4⟩
  word := [1,2,0]
  edges k := match k.val with
    | 0 => .core 5 ⟨0,false⟩
    | 1 => .core 14 ⟨0,false⟩
    | 2 => .boundary { kind := .unit 1 3, quiver := ⟨-26,4,-15,-7,-1,4⟩, returnVertex := 2 }
    | _ => .core 9 ⟨21,true⟩

def q066Row11 : CoreRow 25 2 where
  quiver := ⟨2,1,-3,1,6,2⟩
  word := [2,3,0]
  edges k := match k.val with
    | 0 => .core 7 ⟨0,false⟩
    | 1 => .core 15 ⟨0,false⟩
    | 2 => .core 16 ⟨0,false⟩
    | _ => .boundary { kind := .unit 1 2, quiver := ⟨-16,-5,3,1,-6,-2⟩, returnVertex := 3 }

def q066Row12 : CoreRow 25 2 where
  quiver := ⟨-3,2,5,0,-2,3⟩
  word := [3,0,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨3,-2,-5,6,13,3⟩, returnVertex := 0 }
    | 1 => .core 8 ⟨0,false⟩
    | 2 => .core 17 ⟨0,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨7,2,-5,-6,2,-3⟩, returnVertex := 3 }

def q066Row13 : CoreRow 25 2 where
  quiver := ⟨-1,4,2,7,-3,21⟩
  word := [1,0,3,1]
  edges k := match k.val with
    | 0 => .core 18 ⟨0,false⟩
    | 1 => .core 9 ⟨0,false⟩
    | 2 => .boundary { kind := .unit 0 1, quiver := ⟨-1,-4,86,-7,144,-21⟩, returnVertex := 2 }
    | _ => .boundary { kind := .fork, quiver := ⟨5,4,-2,-56,3,-21⟩, returnVertex := 3 }

def q066Row14 : CoreRow 25 2 where
  quiver := ⟨-2,10,1,-7,1,-11⟩
  word := [1,2,0,1]
  edges k := match k.val with
    | 0 => .core 19 ⟨0,false⟩
    | 1 => .core 10 ⟨0,false⟩
    | 2 => .boundary { kind := .unit 0 3, quiver := ⟨68,-10,1,7,-76,11⟩, returnVertex := 2 }
    | _ => .core 18 ⟨11,true⟩

def q066Row15 : CoreRow 25 2 where
  quiver := ⟨-2,3,9,-1,-6,2⟩
  word := [2,3,0,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨2,-3,-9,5,12,2⟩, returnVertex := 0 }
    | 1 => .core 11 ⟨0,false⟩
    | 2 => .core 20 ⟨0,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨52,3,-9,-13,6,-2⟩, returnVertex := 3 }

def q066Row16 : CoreRow 25 2 where
  quiver := ⟨2,-1,-1,-1,8,-2⟩
  word := [2,3,0,2]
  edges k := match k.val with
    | 0 => .core 11 ⟨16,true⟩
    | 1 => .core 21 ⟨0,false⟩
    | 2 => .core 11 ⟨0,false⟩
    | _ => .core 21 ⟨16,true⟩

def q066Row17 : CoreRow 25 2 where
  quiver := ⟨-3,-2,11,0,-2,-3⟩
  word := [3,0,1,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .diamond 1 2, quiver := ⟨3,2,-11,0,31,19⟩, returnVertex := 0 }
    | 1 => .core 12 ⟨23,true⟩
    | 2 => .core 12 ⟨0,false⟩
    | _ => .boundary { kind := .diamond 1 2, quiver := ⟨19,31,-11,0,2,3⟩, returnVertex := 3 }

def q066Row18 : CoreRow 25 2 where
  quiver := ⟨1,-4,-2,11,-1,21⟩
  word := [1,0,3,1,0]
  edges k := match k.val with
    | 0 => .core 13 ⟨0,false⟩
    | 1 => .core 14 ⟨19,true⟩
    | 2 => .boundary { kind := .fork, quiver := ⟨-43,4,-2,-11,230,-21⟩, returnVertex := 2 }
    | _ => .core 22 ⟨0,false⟩

def q066Row19 : CoreRow 25 2 where
  quiver := ⟨2,-10,-1,13,3,-11⟩
  word := [1,2,0,1,0]
  edges k := match k.val with
    | 0 => .core 14 ⟨0,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨-2,16,5,-13,-3,-11⟩, returnVertex := 1 }
    | 2 => .boundary { kind := .fork, quiver := ⟨-128,10,-111,-13,3,11⟩, returnVertex := 2 }
    | _ => .core 23 ⟨0,false⟩

def q066Row20 : CoreRow 25 2 where
  quiver := ⟨1,-3,15,1,-6,-2⟩
  word := [2,3,0,1,2]
  edges k := match k.val with
    | 0 => .core 24 ⟨0,false⟩
    | 1 => .core 21 ⟨2,false⟩
    | 2 => .core 15 ⟨0,false⟩
    | _ => .boundary { kind := .unit 1 2, quiver := ⟨91,27,-15,1,6,2⟩, returnVertex := 3 }

def q066Row21 : CoreRow 25 2 where
  quiver := ⟨-2,-1,15,1,-8,6⟩
  word := [2,3,0,2,1]
  edges k := match k.val with
    | 0 => .mstrip 0 (0) 1 ⟨2,false⟩
    | 1 => .core 16 ⟨0,false⟩
    | 2 => .core 20 ⟨2,false⟩
    | _ => .boundary { kind := .unit 0 2, quiver := ⟨118,-1,-15,-47,8,-6⟩, returnVertex := 3 }

def q066Row22 : CoreRow 25 2 where
  quiver := ⟨1,-46,2,-10,1,-21⟩
  word := [1,0,3,1,0,3]
  edges k := match k.val with
    | 0 => .mstrip 1 (0) 1 ⟨1,true⟩
    | 1 => .core 23 ⟨6,true⟩
    | 2 => .boundary { kind := .unit 0 1, quiver := ⟨1,46,-964,10,-209,21⟩, returnVertex := 2 }
    | _ => .core 18 ⟨0,false⟩

def q066Row23 : CoreRow 25 2 where
  quiver := ⟨-1,-10,1,46,-3,11⟩
  word := [1,2,0,1,0,3]
  edges k := match k.val with
    | 0 => .core 22 ⟨6,true⟩
    | 1 => .core 25 ⟨0,true⟩
    | 2 => .boundary { kind := .unit 0 3, quiver := ⟨-461,10,1,-46,503,-11⟩, returnVertex := 2 }
    | _ => .core 19 ⟨0,false⟩

def q066Row24 : CoreRow 25 2 where
  quiver := ⟨-1,3,-15,-2,-6,43⟩
  word := [2,3,0,1,2,0]
  edges k := match k.val with
    | 0 => .core 20 ⟨0,false⟩
    | 1 => .mstrip 0 (0) 2 ⟨6,false⟩
    | 2 => .boundary { kind := .fork, quiver := ⟨5,-3,114,2,-6,-43⟩, returnVertex := 2 }
    | _ => .boundary { kind := .unit 0 1, quiver := ⟨-1,-642,15,-260,6,-43⟩, returnVertex := 3 }

def q066Row25 : CoreRow 25 2 where
  quiver := ⟨-1,10,2,46,-3,127⟩
  word := [1,0,3,1,0,3,0,1,0]
  edges k := match k.val with
    | 0 => .mstrip 1 (0) 2 ⟨1,true⟩
    | 1 => .core 23 ⟨0,true⟩
    | 2 => .boundary { kind := .unit 0 1, quiver := ⟨-1,-10,1272,-46,5839,-127⟩, returnVertex := 2 }
    | _ => .boundary { kind := .fork, quiver := ⟨5,10,-2,-335,3,-127⟩, returnVertex := 3 }

def q066 : Certificate where
  initial := ⟨-2,-2,-1,-1,1,-1⟩
  entryWord := []
  entryFrame := ⟨0,false⟩
  size := 25
  stripCount := 2
  core i := match i.val with
    | 0 => q066Row0
    | 1 => q066Row1
    | 2 => q066Row2
    | 3 => q066Row3
    | 4 => q066Row4
    | 5 => q066Row5
    | 6 => q066Row6
    | 7 => q066Row7
    | 8 => q066Row8
    | 9 => q066Row9
    | 10 => q066Row10
    | 11 => q066Row11
    | 12 => q066Row12
    | 13 => q066Row13
    | 14 => q066Row14
    | 15 => q066Row15
    | 16 => q066Row16
    | 17 => q066Row17
    | 18 => q066Row18
    | 19 => q066Row19
    | 20 => q066Row20
    | 21 => q066Row21
    | 22 => q066Row22
    | 23 => q066Row23
    | 24 => q066Row24
    | _ => q066Row25
  strips i := match i.val with
    | 0 => q066Strip0
    | _ => q066Strip1
  triangleAvoidance := true

def q070Row0 : CoreRow 14 0 where
  quiver := ⟨-2,-2,-1,-1,2,-2⟩
  word := []
  edges k := match k.val with
    | 0 => .core 0 ⟨2,true⟩
    | 1 => .core 1 ⟨0,false⟩
    | 2 => .core 2 ⟨0,false⟩
    | _ => .core 3 ⟨0,false⟩

def q070Row1 : CoreRow 14 0 where
  quiver := ⟨2,-4,-1,1,-2,0⟩
  word := [1]
  edges k := match k.val with
    | 0 => .core 4 ⟨0,false⟩
    | 1 => .core 0 ⟨0,false⟩
    | 2 => .core 5 ⟨0,false⟩
    | _ => .core 5 ⟨0,true⟩

def q070Row2 : CoreRow 14 0 where
  quiver := ⟨-2,2,-5,1,0,2⟩
  word := [2]
  edges k := match k.val with
    | 0 => .boundary { kind := .diamond 1 3, quiver := ⟨2,-2,5,5,0,-8⟩, returnVertex := 0 }
    | 1 => .core 6 ⟨0,false⟩
    | 2 => .core 0 ⟨0,false⟩
    | _ => .core 7 ⟨0,false⟩

def q070Row3 : CoreRow 14 0 where
  quiver := ⟨-4,-2,1,3,-2,2⟩
  word := [3]
  edges k := match k.val with
    | 0 => .core 8 ⟨0,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨4,-2,-7,-3,2,-4⟩, returnVertex := 1 }
    | 2 => .boundary { kind := .unit 0 3, quiver := ⟨-10,2,1,-3,4,-2⟩, returnVertex := 2 }
    | _ => .core 0 ⟨0,false⟩

def q070Row4 : CoreRow 14 0 where
  quiver := ⟨-2,4,1,-7,-4,0⟩
  word := [1,0]
  edges k := match k.val with
    | 0 => .core 1 ⟨0,false⟩
    | 1 => .boundary { kind := .diamond 2 3, quiver := ⟨2,-10,-7,7,4,0⟩, returnVertex := 1 }
    | 2 => .zero (4) (4) (7) (26) { phase := 0, returnVertex := 2, frame := ⟨23,true⟩, alternateTarget := 9, alternateFrame := ⟨0,false⟩ }
    | _ => .core 9 ⟨0,false⟩

def q070Row5 : CoreRow 14 0 where
  quiver := ⟨-2,4,-1,-1,-2,0⟩
  word := [1,2]
  edges k := match k.val with
    | 0 => .core 10 ⟨0,false⟩
    | 1 => .core 6 ⟨2,false⟩
    | 2 => .core 1 ⟨0,false⟩
    | _ => .core 1 ⟨0,true⟩

def q070Row6 : CoreRow 14 0 where
  quiver := ⟨2,2,-5,-1,0,2⟩
  word := [2,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 2, quiver := ⟨-2,-2,5,-1,-10,-8⟩, returnVertex := 0 }
    | 1 => .core 2 ⟨0,false⟩
    | 2 => .core 5 ⟨2,false⟩
    | _ => .core 11 ⟨0,false⟩

def q070Row7 : CoreRow 14 0 where
  quiver := ⟨-2,-8,5,1,0,-2⟩
  word := [2,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 2, quiver := ⟨2,8,-5,1,10,38⟩, returnVertex := 0 }
    | 1 => .core 11 ⟨0,false⟩
    | 2 => .core 12 ⟨0,false⟩
    | _ => .core 2 ⟨0,false⟩

def q070Row8 : CoreRow 14 0 where
  quiver := ⟨4,2,-1,3,2,4⟩
  word := [3,0]
  edges k := match k.val with
    | 0 => .core 3 ⟨0,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨-4,14,7,-3,-2,4⟩, returnVertex := 1 }
    | 2 => .boundary { kind := .fork, quiver := ⟨4,-2,7,-3,14,-4⟩, returnVertex := 2 }
    | _ => .core 3 ⟨23,true⟩

def q070Row9 : CoreRow 14 0 where
  quiver := ⟨2,4,-1,-7,4,0⟩
  word := [1,0,3]
  edges k := match k.val with
    | 0 => .core 10 ⟨21,true⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨-2,4,7,7,-4,28⟩, returnVertex := 1 }
    | 2 => .zero (4) (4) (7) (26) { phase := 1, returnVertex := 2, frame := ⟨23,true⟩, alternateTarget := 4, alternateFrame := ⟨0,false⟩ }
    | _ => .core 4 ⟨0,false⟩

def q070Row10 : CoreRow 14 0 where
  quiver := ⟨2,-4,1,7,-2,-4⟩
  word := [1,2,0]
  edges k := match k.val with
    | 0 => .core 5 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 0 3, quiver := ⟨-2,10,1,-7,2,-18⟩, returnVertex := 1 }
    | 2 => .boundary { kind := .fork, quiver := ⟨-26,4,-15,-7,-2,4⟩, returnVertex := 2 }
    | _ => .core 9 ⟨21,true⟩

def q070Row11 : CoreRow 14 0 where
  quiver := ⟨2,-8,5,-1,0,-2⟩
  word := [2,1,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .diamond 1 3, quiver := ⟨-2,8,-5,-17,0,38⟩, returnVertex := 0 }
    | 1 => .core 7 ⟨0,false⟩
    | 2 => .core 13 ⟨0,false⟩
    | _ => .core 6 ⟨0,false⟩

def q070Row12 : CoreRow 14 0 where
  quiver := ⟨-10,8,-11,-1,0,2⟩
  word := [2,3,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .diamond 1 3, quiver := ⟨10,-8,11,79,0,-86⟩, returnVertex := 0 }
    | 1 => .core 14 ⟨0,false⟩
    | 2 => .core 7 ⟨0,false⟩
    | _ => .zero (2) (10) (11) (14) { phase := 0, returnVertex := 3, frame := ⟨10,true⟩, alternateTarget := 14, alternateFrame := ⟨0,false⟩ }

def q070Row13 : CoreRow 14 0 where
  quiver := ⟨2,8,-11,1,-2,2⟩
  word := [2,1,3,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 2, quiver := ⟨-2,-8,11,1,-24,-86⟩, returnVertex := 0 }
    | 1 => .core 14 ⟨2,false⟩
    | 2 => .core 11 ⟨0,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨2,-14,11,-3,2,-2⟩, returnVertex := 3 }

def q070Row14 : CoreRow 14 0 where
  quiver := ⟨10,-2,-11,1,0,2⟩
  word := [2,3,2,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨-10,2,11,-19,-110,2⟩, returnVertex := 0 }
    | 1 => .core 12 ⟨0,false⟩
    | 2 => .core 13 ⟨2,false⟩
    | _ => .zero (2) (10) (11) (14) { phase := 1, returnVertex := 3, frame := ⟨10,true⟩, alternateTarget := 12, alternateFrame := ⟨0,false⟩ }

def q070 : Certificate where
  initial := ⟨-2,-2,-1,-1,2,-2⟩
  entryWord := []
  entryFrame := ⟨0,false⟩
  size := 14
  stripCount := 0
  core i := match i.val with
    | 0 => q070Row0
    | 1 => q070Row1
    | 2 => q070Row2
    | 3 => q070Row3
    | 4 => q070Row4
    | 5 => q070Row5
    | 6 => q070Row6
    | 7 => q070Row7
    | 8 => q070Row8
    | 9 => q070Row9
    | 10 => q070Row10
    | 11 => q070Row11
    | 12 => q070Row12
    | 13 => q070Row13
    | _ => q070Row14
  strips := Fin.elim0
  triangleAvoidance := true

def q179Strip0 : StripRecord 88 where
  m := (2)
  a := (26)
  b := (4)
  c := (11)
  rootCore := 34
  rootQuiver := ⟨11,-4,-26,1,2,1⟩
  rootWord := [1,3,2,1]
  rootFrame := ⟨23,false⟩
  backward p := match p.val with
    | 0 => ⟨33,⟨21,false⟩⟩
    | 1 => ⟨22,⟨23,false⟩⟩
    | _ => ⟨49,⟨19,false⟩⟩

def q179Strip1 : StripRecord 88 where
  m := (2)
  a := (12)
  b := (6)
  c := (7)
  rootCore := 48
  rootQuiver := ⟨12,-1,-2,-6,7,-1⟩
  rootWord := [0,3,2,0,3]
  rootFrame := ⟨3,false⟩
  backward p := match p.val with
    | 0 => ⟨55,⟨10,false⟩⟩
    | 1 => ⟨32,⟨4,false⟩⟩
    | _ => ⟨64,⟨4,false⟩⟩

def q179Strip2 : StripRecord 88 where
  m := (6)
  a := (73)
  b := (9)
  c := (12)
  rootCore := 70
  rootQuiver := ⟨6,-73,1,12,-1,9⟩
  rootWord := [3,0,2,0,3,1]
  rootFrame := ⟨4,true⟩
  backward p := match p.val with
    | 0 => ⟨69,⟨1,true⟩⟩
    | 1 => ⟨55,⟨3,true⟩⟩
    | _ => ⟨81,⟨7,true⟩⟩

def q179Strip3 : StripRecord 88 where
  m := (6)
  a := (107)
  b := (16)
  c := (18)
  rootCore := 72
  rootQuiver := ⟨6,-18,1,107,-1,-16⟩
  rootWord := [3,0,2,1,3,0]
  rootFrame := ⟨10,false⟩
  backward p := match p.val with
    | 0 => ⟨71,⟨7,false⟩⟩
    | 1 => ⟨57,⟨13,false⟩⟩
    | _ => ⟨82,⟨1,false⟩⟩

def q179Strip4 : StripRecord 88 where
  m := (2)
  a := (35)
  b := (12)
  c := (18)
  rootCore := 73
  rootQuiver := ⟨12,-18,35,1,-1,-2⟩
  rootWord := [3,0,2,1,3,2]
  rootFrame := ⟨21,true⟩
  backward p := match p.val with
    | 0 => ⟨78,⟨6,true⟩⟩
    | 1 => ⟨57,⟨21,true⟩⟩
    | _ => ⟨83,⟨21,true⟩⟩

def q179Strip5 : StripRecord 88 where
  m := (2)
  a := (53)
  b := (11)
  c := (24)
  rootCore := 77
  rootQuiver := ⟨-53,2,1,-24,11,-1⟩
  rootWord := [0,1,0,2,0,3,2]
  rootFrame := ⟨5,true⟩
  backward p := match p.val with
    | 0 => ⟨76,⟨4,true⟩⟩
    | 1 => ⟨62,⟨5,true⟩⟩
    | _ => ⟨86,⟨10,true⟩⟩

def q179Strip6 : StripRecord 88 where
  m := (8)
  a := (2741)
  b := (299)
  c := (342)
  rootCore := 80
  rootQuiver := ⟨2741,-8,-1,342,-299,1⟩
  rootWord := [2,0,1,2,0,3,2]
  rootFrame := ⟨5,false⟩
  backward p := match p.val with
    | 0 => ⟨79,⟨4,false⟩⟩
    | 1 => ⟨67,⟨5,false⟩⟩
    | _ => ⟨87,⟨10,false⟩⟩

def q179Strip7 : StripRecord 88 where
  m := (8)
  a := (794)
  b := (86)
  c := (99)
  rootCore := 85
  rootQuiver := ⟨99,-8,-1,794,86,1⟩
  rootWord := [0,1,0,1,0,2,3,0]
  rootFrame := ⟨16,true⟩
  backward p := match p.val with
    | 0 => ⟨84,⟨10,true⟩⟩
    | 1 => ⟨75,⟨16,true⟩⟩
    | _ => ⟨88,⟨4,true⟩⟩

def q179Row0 : CoreRow 88 8 where
  quiver := ⟨-2,-2,1,-1,-2,1⟩
  word := []
  edges k := match k.val with
    | 0 => .core 1 ⟨0,false⟩
    | 1 => .core 2 ⟨0,false⟩
    | 2 => .core 3 ⟨0,false⟩
    | _ => .core 4 ⟨0,false⟩

def q179Row1 : CoreRow 88 8 where
  quiver := ⟨2,2,-1,-1,0,3⟩
  word := [0]
  edges k := match k.val with
    | 0 => .core 0 ⟨0,false⟩
    | 1 => .core 5 ⟨0,false⟩
    | 2 => .core 6 ⟨0,false⟩
    | _ => .core 7 ⟨0,false⟩

def q179Row2 : CoreRow 88 8 where
  quiver := ⟨2,-4,-3,1,2,1⟩
  word := [1]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 2 3, quiver := ⟨-2,4,3,-7,-4,1⟩, returnVertex := 0 }
    | 1 => .core 0 ⟨0,false⟩
    | 2 => .core 8 ⟨0,false⟩
    | _ => .core 9 ⟨0,false⟩

def q179Row3 : CoreRow 88 8 where
  quiver := ⟨-2,2,1,1,-2,-1⟩
  word := [2]
  edges k := match k.val with
    | 0 => .core 10 ⟨0,false⟩
    | 1 => .core 11 ⟨0,false⟩
    | 2 => .core 0 ⟨0,false⟩
    | _ => .core 12 ⟨0,false⟩

def q179Row4 : CoreRow 88 8 where
  quiver := ⟨0,-2,-1,-3,2,-1⟩
  word := [3]
  edges k := match k.val with
    | 0 => .core 13 ⟨0,false⟩
    | 1 => .core 14 ⟨0,false⟩
    | 2 => .core 15 ⟨0,false⟩
    | _ => .core 0 ⟨0,false⟩

def q179Row5 : CoreRow 88 8 where
  quiver := ⟨-2,2,-1,1,0,3⟩
  word := [0,1]
  edges k := match k.val with
    | 0 => .core 16 ⟨0,false⟩
    | 1 => .core 1 ⟨0,false⟩
    | 2 => .core 17 ⟨0,false⟩
    | _ => .core 12 ⟨21,false⟩

def q179Row6 : CoreRow 88 8 where
  quiver := ⟨4,-2,5,1,0,-3⟩
  word := [0,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .diamond 1 3, quiver := ⟨-4,2,-5,-7,0,7⟩, returnVertex := 0 }
    | 1 => .core 18 ⟨0,false⟩
    | 2 => .core 1 ⟨0,false⟩
    | _ => .zero (3) (4) (5) (13) { phase := 0, returnVertex := 3, frame := ⟨10,false⟩, alternateTarget := 18, alternateFrame := ⟨0,false⟩ }

def q179Row7 : CoreRow 88 8 where
  quiver := ⟨2,-1,1,-1,0,-3⟩
  word := [0,3]
  edges k := match k.val with
    | 0 => .core 13 ⟨21,false⟩
    | 1 => .core 12 ⟨21,false⟩
    | 2 => .core 19 ⟨0,false⟩
    | _ => .core 1 ⟨0,false⟩

def q179Row8 : CoreRow 88 8 where
  quiver := ⟨-2,4,-3,-1,3,-1⟩
  word := [1,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨2,-4,3,7,3,-13⟩, returnVertex := 0 }
    | 1 => .core 11 ⟨2,false⟩
    | 2 => .core 2 ⟨0,false⟩
    | _ => .core 20 ⟨0,false⟩

def q179Row9 : CoreRow 88 8 where
  quiver := ⟨-4,-7,3,1,-2,-1⟩
  word := [1,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 2, quiver := ⟨4,7,-3,1,10,20⟩, returnVertex := 0 }
    | 1 => .core 21 ⟨0,false⟩
    | 2 => .core 22 ⟨0,false⟩
    | _ => .core 2 ⟨0,false⟩

def q179Row10 : CoreRow 88 8 where
  quiver := ⟨2,-2,-1,5,0,-1⟩
  word := [2,0]
  edges k := match k.val with
    | 0 => .core 3 ⟨0,false⟩
    | 1 => .core 23 ⟨0,false⟩
    | 2 => .core 24 ⟨0,false⟩
    | _ => .core 16 ⟨0,false⟩

def q179Row11 : CoreRow 88 8 where
  quiver := ⟨2,2,-3,-1,2,-3⟩
  word := [2,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 2, quiver := ⟨-2,-2,3,-1,-4,-9⟩, returnVertex := 0 }
    | 1 => .core 3 ⟨0,false⟩
    | 2 => .core 8 ⟨2,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨-4,2,3,5,-2,3⟩, returnVertex := 3 }

def q179Row12 : CoreRow 88 8 where
  quiver := ⟨0,3,-1,1,2,1⟩
  word := [2,3]
  edges k := match k.val with
    | 0 => .core 5 ⟨21,false⟩
    | 1 => .core 7 ⟨21,false⟩
    | 2 => .core 15 ⟨1,false⟩
    | _ => .core 3 ⟨0,false⟩

def q179Row13 : CoreRow 88 8 where
  quiver := ⟨0,2,1,-3,2,-1⟩
  word := [3,0]
  edges k := match k.val with
    | 0 => .core 4 ⟨0,false⟩
    | 1 => .core 25 ⟨0,false⟩
    | 2 => .core 26 ⟨0,false⟩
    | _ => .core 7 ⟨21,false⟩

def q179Row14 : CoreRow 88 8 where
  quiver := ⟨0,-2,-1,3,-2,5⟩
  word := [3,1]
  edges k := match k.val with
    | 0 => .core 25 ⟨0,false⟩
    | 1 => .core 4 ⟨0,false⟩
    | 2 => .boundary { kind := .unit 0 3, quiver := ⟨-6,2,-1,-3,13,-5⟩, returnVertex := 2 }
    | _ => .core 27 ⟨0,false⟩

def q179Row15 : CoreRow 88 8 where
  quiver := ⟨0,2,-3,3,-1,1⟩
  word := [3,2]
  edges k := match k.val with
    | 0 => .core 28 ⟨0,false⟩
    | 1 => .core 29 ⟨0,false⟩
    | 2 => .core 4 ⟨0,false⟩
    | _ => .core 12 ⟨1,false⟩

def q179Row16 : CoreRow 88 8 where
  quiver := ⟨2,-2,1,5,0,1⟩
  word := [0,1,0]
  edges k := match k.val with
    | 0 => .core 5 ⟨0,false⟩
    | 1 => .core 30 ⟨0,false⟩
    | 2 => .core 31 ⟨0,false⟩
    | _ => .core 10 ⟨0,false⟩

def q179Row17 : CoreRow 88 8 where
  quiver := ⟨-2,-2,5,-1,3,-3⟩
  word := [0,1,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 2, quiver := ⟨2,2,-5,-1,13,7⟩, returnVertex := 0 }
    | 1 => .core 18 ⟨2,false⟩
    | 2 => .core 5 ⟨0,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨-2,13,-5,8,-3,3⟩, returnVertex := 3 }

def q179Row18 : CoreRow 88 8 where
  quiver := ⟨-4,2,5,-1,0,-3⟩
  word := [0,2,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨4,-2,-5,7,20,-3⟩, returnVertex := 0 }
    | 1 => .core 6 ⟨0,false⟩
    | 2 => .core 17 ⟨2,false⟩
    | _ => .zero (3) (4) (5) (13) { phase := 1, returnVertex := 3, frame := ⟨10,false⟩, alternateTarget := 6, alternateFrame := ⟨0,false⟩ }

def q179Row19 : CoreRow 88 8 where
  quiver := ⟨2,1,-2,1,-3,3⟩
  word := [0,3,2]
  edges k := match k.val with
    | 0 => .core 32 ⟨0,false⟩
    | 1 => .core 29 ⟨22,false⟩
    | 2 => .core 7 ⟨0,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨2,-5,2,-8,3,-3⟩, returnVertex := 3 }

def q179Row20 : CoreRow 88 8 where
  quiver := ⟨-11,4,3,2,-3,1⟩
  word := [1,2,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 2 3, quiver := ⟨11,-4,-3,46,30,1⟩, returnVertex := 0 }
    | 1 => .boundary { kind := .fork, quiver := ⟨11,4,-30,-2,3,-5⟩, returnVertex := 1 }
    | 2 => .core 22 ⟨1,false⟩
    | _ => .core 8 ⟨0,false⟩

def q179Row21 : CoreRow 88 8 where
  quiver := ⟨4,-7,-5,-1,2,-3⟩
  word := [1,3,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨-4,7,5,-29,-18,-3⟩, returnVertex := 0 }
    | 1 => .core 9 ⟨0,false⟩
    | 2 => .core 33 ⟨0,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨-6,-7,5,5,-2,3⟩, returnVertex := 3 }

def q179Row22 : CoreRow 88 8 where
  quiver := ⟨-11,7,-4,-1,-2,1⟩
  word := [1,3,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨11,-7,4,76,-2,-27⟩, returnVertex := 0 }
    | 1 => .core 34 ⟨0,false⟩
    | 2 => .core 9 ⟨0,false⟩
    | _ => .core 20 ⟨1,false⟩

def q179Row23 : CoreRow 88 8 where
  quiver := ⟨-2,8,-1,-5,0,-1⟩
  word := [2,0,1]
  edges k := match k.val with
    | 0 => .core 35 ⟨0,false⟩
    | 1 => .core 10 ⟨0,false⟩
    | 2 => .core 36 ⟨0,false⟩
    | _ => .core 30 ⟨0,false⟩

def q179Row24 : CoreRow 88 8 where
  quiver := ⟨-8,2,-3,-5,0,1⟩
  word := [2,0,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .diamond 1 3, quiver := ⟨8,-2,3,11,0,-5⟩, returnVertex := 0 }
    | 1 => .zero (5) (3) (8) (38) { phase := 0, returnVertex := 1, frame := ⟨20,true⟩, alternateTarget := 37, alternateFrame := ⟨0,false⟩ }
    | 2 => .core 10 ⟨0,false⟩
    | _ => .core 37 ⟨0,false⟩

def q179Row25 : CoreRow 88 8 where
  quiver := ⟨0,2,1,3,-2,5⟩
  word := [3,0,1]
  edges k := match k.val with
    | 0 => .core 14 ⟨0,false⟩
    | 1 => .core 13 ⟨0,false⟩
    | 2 => .boundary { kind := .diamond 0 1, quiver := ⟨0,-2,11,-3,13,-5⟩, returnVertex := 2 }
    | _ => .core 38 ⟨0,false⟩

def q179Row26 : CoreRow 88 8 where
  quiver := ⟨6,-2,1,3,-1,1⟩
  word := [3,0,2]
  edges k := match k.val with
    | 0 => .core 39 ⟨0,false⟩
    | 1 => .core 40 ⟨0,false⟩
    | 2 => .core 13 ⟨0,false⟩
    | _ => .core 32 ⟨15,false⟩

def q179Row27 : CoreRow 88 8 where
  quiver := ⟨0,-7,1,-7,2,-5⟩
  word := [3,1,3]
  edges k := match k.val with
    | 0 => .core 41 ⟨0,false⟩
    | 1 => .zero (2) (7) (7) (9) { phase := 0, returnVertex := 1, frame := ⟨0,false⟩, alternateTarget := 41, alternateFrame := ⟨0,false⟩ }
    | 2 => .boundary { kind := .diamond 0 1, quiver := ⟨0,7,-34,7,-33,5⟩, returnVertex := 2 }
    | _ => .core 14 ⟨0,false⟩

def q179Row28 : CoreRow 88 8 where
  quiver := ⟨0,-2,3,3,-1,-5⟩
  word := [3,2,0]
  edges k := match k.val with
    | 0 => .core 15 ⟨0,false⟩
    | 1 => .core 42 ⟨0,false⟩
    | 2 => .boundary { kind := .unit 1 3, quiver := ⟨-6,2,-7,-3,-1,5⟩, returnVertex := 2 }
    | _ => .core 43 ⟨0,false⟩

def q179Row29 : CoreRow 88 8 where
  quiver := ⟨0,2,-3,-3,1,-2⟩
  word := [3,2,1]
  edges k := match k.val with
    | 0 => .core 42 ⟨0,false⟩
    | 1 => .core 15 ⟨0,false⟩
    | 2 => .boundary { kind := .fork, quiver := ⟨6,-2,-3,3,-5,2⟩, returnVertex := 2 }
    | _ => .core 19 ⟨17,false⟩

def q179Row30 : CoreRow 88 8 where
  quiver := ⟨-2,8,1,-5,0,1⟩
  word := [0,1,0,1]
  edges k := match k.val with
    | 0 => .core 44 ⟨0,false⟩
    | 1 => .core 16 ⟨0,false⟩
    | 2 => .core 45 ⟨0,false⟩
    | _ => .core 23 ⟨0,false⟩

def q179Row31 : CoreRow 88 8 where
  quiver := ⟨-8,2,1,-5,5,-1⟩
  word := [0,1,0,2]
  edges k := match k.val with
    | 0 => .core 46 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 0 3, quiver := ⟨8,-38,1,5,-5,24⟩, returnVertex := 1 }
    | 2 => .core 16 ⟨0,false⟩
    | _ => .core 37 ⟨1,false⟩

def q179Row32 : CoreRow 88 8 where
  quiver := ⟨-2,-1,2,1,-7,1⟩
  word := [0,3,2,0]
  edges k := match k.val with
    | 0 => .core 19 ⟨0,false⟩
    | 1 => .core 47 ⟨0,false⟩
    | 2 => .core 26 ⟨20,false⟩
    | _ => .core 48 ⟨0,false⟩

def q179Row33 : CoreRow 88 8 where
  quiver := ⟨4,7,-26,1,-1,3⟩
  word := [1,3,1,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 2, quiver := ⟨-4,-7,26,1,-105,-179⟩, returnVertex := 0 }
    | 1 => .core 34 ⟨2,false⟩
    | 2 => .core 21 ⟨0,false⟩
    | _ => .core 49 ⟨0,false⟩

def q179Row34 : CoreRow 88 8 where
  quiver := ⟨11,-4,-26,1,2,1⟩
  word := [1,3,2,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 2 3, quiver := ⟨-11,4,26,-43,-284,1⟩, returnVertex := 0 }
    | 1 => .core 22 ⟨0,false⟩
    | 2 => .core 33 ⟨2,false⟩
    | _ => .mstrip 0 (0) 1 ⟨23,false⟩

def q179Row35 : CoreRow 88 8 where
  quiver := ⟨2,-8,1,11,0,-9⟩
  word := [2,0,1,0]
  edges k := match k.val with
    | 0 => .core 23 ⟨0,false⟩
    | 1 => .zero (2) (9) (11) (14) { phase := 0, returnVertex := 1, frame := ⟨21,true⟩, alternateTarget := 50, alternateFrame := ⟨0,false⟩ }
    | 2 => .boundary { kind := .diamond 1 3, quiver := ⟨-86,8,-71,-11,0,9⟩, returnVertex := 2 }
    | _ => .core 50 ⟨0,false⟩

def q179Row36 : CoreRow 88 8 where
  quiver := ⟨38,-8,-1,5,-5,1⟩
  word := [2,0,1,2]
  edges k := match k.val with
    | 0 => .core 51 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 0 3, quiver := ⟨-38,182,-1,-5,5,-24⟩, returnVertex := 1 }
    | 2 => .core 23 ⟨0,false⟩
    | _ => .core 52 ⟨0,false⟩

def q179Row37 : CoreRow 88 8 where
  quiver := ⟨-8,-1,3,-5,0,-1⟩
  word := [2,0,2,3]
  edges k := match k.val with
    | 0 => .core 53 ⟨0,false⟩
    | 1 => .zero (5) (3) (8) (38) { phase := 1, returnVertex := 1, frame := ⟨20,true⟩, alternateTarget := 24, alternateFrame := ⟨0,false⟩ }
    | 2 => .core 31 ⟨1,false⟩
    | _ => .core 24 ⟨0,false⟩

def q179Row38 : CoreRow 88 8 where
  quiver := ⟨2,2,-1,-7,2,-5⟩
  word := [3,0,1,3]
  edges k := match k.val with
    | 0 => .core 41 ⟨21,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨-2,2,3,7,-2,9⟩, returnVertex := 1 }
    | 2 => .boundary { kind := .unit 0 3, quiver := ⟨16,-2,-1,7,-33,5⟩, returnVertex := 2 }
    | _ => .core 25 ⟨0,false⟩

def q179Row39 : CoreRow 88 8 where
  quiver := ⟨-6,2,-1,-9,-1,3⟩
  word := [3,0,2,0]
  edges k := match k.val with
    | 0 => .core 26 ⟨0,false⟩
    | 1 => .core 54 ⟨0,false⟩
    | 2 => .boundary { kind := .unit 1 3, quiver := ⟨12,-2,5,9,-1,-3⟩, returnVertex := 2 }
    | _ => .core 55 ⟨0,false⟩

def q179Row40 : CoreRow 88 8 where
  quiver := ⟨-6,16,1,-3,1,-2⟩
  word := [3,0,2,1]
  edges k := match k.val with
    | 0 => .core 56 ⟨0,false⟩
    | 1 => .core 26 ⟨0,false⟩
    | 2 => .boundary { kind := .unit 0 3, quiver := ⟨42,-16,1,3,-5,2⟩, returnVertex := 2 }
    | _ => .core 57 ⟨0,false⟩

def q179Row41 : CoreRow 88 8 where
  quiver := ⟨0,7,-1,-7,2,2⟩
  word := [3,1,3,0]
  edges k := match k.val with
    | 0 => .core 27 ⟨0,false⟩
    | 1 => .zero (2) (7) (7) (9) { phase := 1, returnVertex := 1, frame := ⟨0,false⟩, alternateTarget := 27, alternateFrame := ⟨0,false⟩ }
    | 2 => .boundary { kind := .fork, quiver := ⟨49,-7,13,7,2,-2⟩, returnVertex := 2 }
    | _ => .core 38 ⟨21,false⟩

def q179Row42 : CoreRow 88 8 where
  quiver := ⟨0,-2,3,-3,1,-8⟩
  word := [3,2,0,1]
  edges k := match k.val with
    | 0 => .core 29 ⟨0,false⟩
    | 1 => .core 28 ⟨0,false⟩
    | 2 => .boundary { kind := .diamond 0 1, quiver := ⟨0,2,-13,3,-23,8⟩, returnVertex := 2 }
    | _ => .core 58 ⟨0,false⟩

def q179Row43 : CoreRow 88 8 where
  quiver := ⟨3,13,-3,3,1,5⟩
  word := [3,2,0,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨-3,-13,3,3,-8,-34⟩, returnVertex := 0 }
    | 1 => .core 59 ⟨0,false⟩
    | 2 => .boundary { kind := .fork, quiver := ⟨3,-13,62,-3,16,-5⟩, returnVertex := 2 }
    | _ => .core 28 ⟨0,false⟩

def q179Row44 : CoreRow 88 8 where
  quiver := ⟨2,-8,-1,11,2,1⟩
  word := [0,1,0,1,0]
  edges k := match k.val with
    | 0 => .core 30 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 2 3, quiver := ⟨-2,14,3,-11,-2,1⟩, returnVertex := 1 }
    | 2 => .core 60 ⟨0,false⟩
    | _ => .core 50 ⟨21,false⟩

def q179Row45 : CoreRow 88 8 where
  quiver := ⟨38,-8,9,5,0,-1⟩
  word := [0,1,0,1,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .diamond 1 3, quiver := ⟨-38,8,-9,-299,0,71⟩, returnVertex := 0 }
    | 1 => .zero (5) (9) (38) (182) { phase := 0, returnVertex := 1, frame := ⟨20,false⟩, alternateTarget := 52, alternateFrame := ⟨1,false⟩ }
    | 2 => .core 30 ⟨0,false⟩
    | _ => .core 52 ⟨1,false⟩

def q179Row46 : CoreRow 88 8 where
  quiver := ⟨8,-2,-1,11,13,-1⟩
  word := [0,1,0,2,0]
  edges k := match k.val with
    | 0 => .core 31 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 2 3, quiver := ⟨-8,86,103,-11,-13,-1⟩, returnVertex := 1 }
    | 2 => .core 61 ⟨0,false⟩
    | _ => .core 62 ⟨0,false⟩

def q179Row47 : CoreRow 88 8 where
  quiver := ⟨2,-1,-12,-1,7,-6⟩
  word := [0,3,2,0,1]
  edges k := match k.val with
    | 0 => .core 63 ⟨0,false⟩
    | 1 => .core 32 ⟨0,false⟩
    | 2 => .core 57 ⟨22,false⟩
    | _ => .boundary { kind := .unit 0 2, quiver := ⟨-82,-1,12,41,-7,6⟩, returnVertex := 3 }

def q179Row48 : CoreRow 88 8 where
  quiver := ⟨12,-1,-2,-6,7,-1⟩
  word := [0,3,2,0,3]
  edges k := match k.val with
    | 0 => .mstrip 1 (0) 1 ⟨3,false⟩
    | 1 => .boundary { kind := .unit 0 2, quiver := ⟨-12,-1,82,6,-7,41⟩, returnVertex := 1 }
    | 2 => .core 55 ⟨14,false⟩
    | _ => .core 32 ⟨0,false⟩

def q179Row49 : CoreRow 88 8 where
  quiver := ⟨4,-71,26,-2,1,-3⟩
  word := [1,3,1,2,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 3, quiver := ⟨-4,71,-26,-286,1,1843⟩, returnVertex := 0 }
    | 1 => .mstrip 0 (0) 2 ⟨11,false⟩
    | 2 => .boundary { kind := .fork, quiver := ⟨4,71,-187,2,-5,3⟩, returnVertex := 2 }
    | _ => .core 33 ⟨0,false⟩

def q179Row50 : CoreRow 88 8 where
  quiver := ⟨2,1,-1,11,0,9⟩
  word := [2,0,1,0,3]
  edges k := match k.val with
    | 0 => .core 44 ⟨21,false⟩
    | 1 => .zero (2) (9) (11) (14) { phase := 1, returnVertex := 1, frame := ⟨21,true⟩, alternateTarget := 35, alternateFrame := ⟨0,false⟩ }
    | 2 => .core 65 ⟨0,false⟩
    | _ => .core 35 ⟨0,false⟩

def q179Row51 : CoreRow 88 8 where
  quiver := ⟨-38,8,1,-299,-43,1⟩
  word := [2,0,1,2,0]
  edges k := match k.val with
    | 0 => .core 36 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 2 3, quiver := ⟨38,-11354,-1633,299,43,1⟩, returnVertex := 1 }
    | 2 => .core 66 ⟨0,false⟩
    | _ => .core 67 ⟨0,false⟩

def q179Row52 : CoreRow 88 8 where
  quiver := ⟨38,-9,1,0,5,-1⟩
  word := [2,0,1,2,3]
  edges k := match k.val with
    | 0 => .core 68 ⟨0,false⟩
    | 1 => .zero (5) (9) (38) (182) { phase := 1, returnVertex := 1, frame := ⟨14,false⟩, alternateTarget := 45, alternateFrame := ⟨1,false⟩ }
    | 2 => .core 45 ⟨1,false⟩
    | _ => .core 36 ⟨0,false⟩

def q179Row53 : CoreRow 88 8 where
  quiver := ⟨8,1,-3,-5,24,2⟩
  word := [2,0,2,3,0]
  edges k := match k.val with
    | 0 => .core 37 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 0 2, quiver := ⟨-8,1,189,5,-24,122⟩, returnVertex := 1 }
    | 2 => .core 62 ⟨15,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨-64,-5,3,-5,-24,-2⟩, returnVertex := 3 }

def q179Row54 : CoreRow 88 8 where
  quiver := ⟨6,-52,-7,9,1,3⟩
  word := [3,0,2,0,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨-6,52,7,-303,-41,3⟩, returnVertex := 0 }
    | 1 => .core 39 ⟨0,false⟩
    | 2 => .boundary { kind := .fork, quiver := ⟨-462,52,-7,-9,28,-3⟩, returnVertex := 2 }
    | _ => .core 69 ⟨0,false⟩

def q179Row55 : CoreRow 88 8 where
  quiver := ⟨-6,-1,1,-12,1,-3⟩
  word := [3,0,2,0,3]
  edges k := match k.val with
    | 0 => .core 48 ⟨14,false⟩
    | 1 => .core 70 ⟨0,false⟩
    | 2 => .core 64 ⟨0,false⟩
    | _ => .core 39 ⟨0,false⟩

def q179Row56 : CoreRow 88 8 where
  quiver := ⟨6,-16,-1,93,7,-2⟩
  word := [3,0,2,1,0]
  edges k := match k.val with
    | 0 => .core 40 ⟨0,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨-6,542,41,-93,-7,-2⟩, returnVertex := 1 }
    | 2 => .boundary { kind := .fork, quiver := ⟨-1482,16,-33,-93,7,2⟩, returnVertex := 2 }
    | _ => .core 71 ⟨0,false⟩

def q179Row57 : CoreRow 88 8 where
  quiver := ⟨-6,18,-1,-1,-1,2⟩
  word := [3,0,2,1,3]
  edges k := match k.val with
    | 0 => .core 72 ⟨0,false⟩
    | 1 => .core 47 ⟨17,false⟩
    | 2 => .core 73 ⟨0,false⟩
    | _ => .core 40 ⟨0,false⟩

def q179Row58 : CoreRow 88 8 where
  quiver := ⟨0,22,-3,5,-1,8⟩
  word := [3,2,0,1,3]
  edges k := match k.val with
    | 0 => .zero (3) (5) (22) (58) { phase := 0, returnVertex := 0, frame := ⟨6,true⟩, alternateTarget := 59, alternateFrame := ⟨5,false⟩ }
    | 1 => .core 59 ⟨5,false⟩
    | 2 => .boundary { kind := .diamond 0 1, quiver := ⟨0,-22,173,-5,39,-8⟩, returnVertex := 2 }
    | _ => .core 42 ⟨0,false⟩

def q179Row59 : CoreRow 88 8 where
  quiver := ⟨-3,22,0,-3,-1,5⟩
  word := [3,2,0,3,1]
  edges k := match k.val with
    | 0 => .zero (3) (5) (22) (58) { phase := 1, returnVertex := 0, frame := ⟨19,true⟩, alternateTarget := 58, alternateFrame := ⟨5,false⟩ }
    | 1 => .core 43 ⟨0,false⟩
    | 2 => .boundary { kind := .unit 1 3, quiver := ⟨63,-22,110,3,-1,-5⟩, returnVertex := 2 }
    | _ => .core 58 ⟨5,false⟩

def q179Row60 : CoreRow 88 8 where
  quiver := ⟨-86,8,-1,-11,13,-1⟩
  word := [0,1,0,1,0,2]
  edges k := match k.val with
    | 0 => .core 74 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 0 3, quiver := ⟨86,-938,-1,11,-13,142⟩, returnVertex := 1 }
    | 2 => .core 44 ⟨0,false⟩
    | _ => .core 75 ⟨0,false⟩

def q179Row61 : CoreRow 88 8 where
  quiver := ⟨-14,2,-3,-11,13,1⟩
  word := [0,1,0,2,0,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨14,-2,3,17,13,-5⟩, returnVertex := 0 }
    | 1 => .boundary { kind := .fork, quiver := ⟨14,-152,-3,11,-13,144⟩, returnVertex := 1 }
    | 2 => .core 46 ⟨0,false⟩
    | _ => .core 76 ⟨0,false⟩

def q179Row62 : CoreRow 88 8 where
  quiver := ⟨-5,-2,1,24,-13,1⟩
  word := [0,1,0,2,0,3]
  edges k := match k.val with
    | 0 => .core 53 ⟨20,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨5,-2,-64,-24,13,-311⟩, returnVertex := 1 }
    | 2 => .core 77 ⟨0,false⟩
    | _ => .core 46 ⟨0,false⟩

def q179Row63 : CoreRow 88 8 where
  quiver := ⟨-2,1,12,-3,-17,-6⟩
  word := [0,3,2,0,1,0]
  edges k := match k.val with
    | 0 => .core 47 ⟨0,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨2,-5,-22,3,17,-6⟩, returnVertex := 1 }
    | 2 => .core 78 ⟨0,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨202,73,-12,-3,17,6⟩, returnVertex := 3 }

def q179Row64 : CoreRow 88 8 where
  quiver := ⟨-6,1,-2,12,-35,3⟩
  word := [0,3,2,0,3,0,2,0]
  edges k := match k.val with
    | 0 => .mstrip 1 (0) 2 ⟨3,false⟩
    | 1 => .boundary { kind := .unit 0 2, quiver := ⟨6,1,-212,-12,35,-417⟩, returnVertex := 1 }
    | 2 => .core 55 ⟨0,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨-6,-5,2,-93,35,-3⟩, returnVertex := 3 }

def q179Row65 : CoreRow 88 8 where
  quiver := ⟨2,-1,8,-11,99,-9⟩
  word := [2,0,1,0,3,2]
  edges k := match k.val with
    | 0 => .core 75 ⟨20,false⟩
    | 1 => .boundary { kind := .unit 0 2, quiver := ⟨-2,-1,206,11,-99,1080⟩, returnVertex := 1 }
    | 2 => .core 50 ⟨0,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨2,71,-8,880,-99,9⟩, returnVertex := 3 }

def q179Row66 : CoreRow 88 8 where
  quiver := ⟨2354,-8,9,299,-43,-1⟩
  word := [2,0,1,2,0,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨-2354,8,-9,-18533,-43,71⟩, returnVertex := 0 }
    | 1 => .boundary { kind := .fork, quiver := ⟨-2354,703838,9,-299,43,-12858⟩, returnVertex := 1 }
    | 2 => .core 51 ⟨0,false⟩
    | _ => .core 79 ⟨0,false⟩

def q179Row67 : CoreRow 88 8 where
  quiver := ⟨5,8,-1,-342,43,-1⟩
  word := [2,0,1,2,0,3]
  edges k := match k.val with
    | 0 => .core 68 ⟨21,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨-5,8,214,342,-43,14705⟩, returnVertex := 1 }
    | 2 => .core 80 ⟨0,false⟩
    | _ => .core 51 ⟨0,false⟩

def q179Row68 : CoreRow 88 8 where
  quiver := ⟨-38,9,-1,-342,5,8⟩
  word := [2,0,1,2,3,0]
  edges k := match k.val with
    | 0 => .core 52 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 0 3, quiver := ⟨38,-12987,-1,342,-5,1718⟩, returnVertex := 1 }
    | 2 => .boundary { kind := .fork, quiver := ⟨3040,-9,71,342,5,-8⟩, returnVertex := 2 }
    | _ => .core 67 ⟨21,false⟩

def q179Row69 : CoreRow 88 8 where
  quiver := ⟨-1,-73,7,9,-1,-3⟩
  word := [3,0,2,0,1,3]
  edges k := match k.val with
    | 0 => .core 81 ⟨0,false⟩
    | 1 => .core 70 ⟨5,false⟩
    | 2 => .boundary { kind := .unit 1 3, quiver := ⟨-658,73,-212,-9,-1,3⟩, returnVertex := 2 }
    | _ => .core 54 ⟨0,false⟩

def q179Row70 : CoreRow 88 8 where
  quiver := ⟨6,-73,1,12,-1,9⟩
  word := [3,0,2,0,3,1]
  edges k := match k.val with
    | 0 => .mstrip 2 (0) 1 ⟨4,true⟩
    | 1 => .core 55 ⟨0,false⟩
    | 2 => .boundary { kind := .unit 0 3, quiver := ⟨-870,73,1,-12,107,-9⟩, returnVertex := 2 }
    | _ => .core 69 ⟨5,false⟩

def q179Row71 : CoreRow 88 8 where
  quiver := ⟨-1,-16,1,107,-7,2⟩
  word := [3,0,2,1,0,3]
  edges k := match k.val with
    | 0 => .core 72 ⟨21,false⟩
    | 1 => .core 82 ⟨0,false⟩
    | 2 => .boundary { kind := .unit 0 3, quiver := ⟨-1713,16,1,-107,207,-2⟩, returnVertex := 2 }
    | _ => .core 56 ⟨0,false⟩

def q179Row72 : CoreRow 88 8 where
  quiver := ⟨6,-18,1,107,-1,-16⟩
  word := [3,0,2,1,3,0]
  edges k := match k.val with
    | 0 => .core 57 ⟨0,false⟩
    | 1 => .mstrip 3 (0) 1 ⟨10,false⟩
    | 2 => .boundary { kind := .unit 1 3, quiver := ⟨-1920,18,-287,-107,-1,16⟩, returnVertex := 2 }
    | _ => .core 71 ⟨21,false⟩

def q179Row73 : CoreRow 88 8 where
  quiver := ⟨12,-18,35,1,-1,-2⟩
  word := [3,0,2,1,3,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 3, quiver := ⟨-12,18,-35,-215,-1,628⟩, returnVertex := 0 }
    | 1 => .core 78 ⟨11,false⟩
    | 2 => .core 57 ⟨0,false⟩
    | _ => .mstrip 4 (0) 1 ⟨21,true⟩

def q179Row74 : CoreRow 88 8 where
  quiver := ⟨86,-8,1,677,13,-9⟩
  word := [0,1,0,1,0,2,0]
  edges k := match k.val with
    | 0 => .core 60 ⟨0,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨-86,58214,1119,-677,-13,-9⟩, returnVertex := 1 }
    | 2 => .boundary { kind := .fork, quiver := ⟨-5330,8,-71,-677,13,9⟩, returnVertex := 2 }
    | _ => .core 84 ⟨0,false⟩

def q179Row75 : CoreRow 88 8 where
  quiver := ⟨-99,8,1,2,-13,1⟩
  word := [0,1,0,1,0,2,3]
  edges k := match k.val with
    | 0 => .core 85 ⟨0,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨99,8,-1286,-2,13,-25⟩, returnVertex := 1 }
    | 2 => .core 65 ⟨15,false⟩
    | _ => .core 60 ⟨0,false⟩

def q179Row76 : CoreRow 88 8 where
  quiver := ⟨-53,-1,3,-11,-13,-1⟩
  word := [0,1,0,2,0,2,3]
  edges k := match k.val with
    | 0 => .core 86 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 2 3, quiver := ⟨53,-584,-686,11,13,-1⟩, returnVertex := 1 }
    | 2 => .core 77 ⟨1,false⟩
    | _ => .core 61 ⟨0,false⟩

def q179Row77 : CoreRow 88 8 where
  quiver := ⟨-53,2,1,-24,11,-1⟩
  word := [0,1,0,2,0,3,2]
  edges k := match k.val with
    | 0 => .mstrip 5 (0) 1 ⟨5,true⟩
    | 1 => .boundary { kind := .unit 0 3, quiver := ⟨53,-1270,1,24,-11,263⟩, returnVertex := 1 }
    | 2 => .core 62 ⟨0,false⟩
    | _ => .core 76 ⟨1,false⟩

def q179Row78 : CoreRow 88 8 where
  quiver := ⟨1,-1,12,3,-35,6⟩
  word := [0,3,2,0,1,0,2]
  edges k := match k.val with
    | 0 => .core 73 ⟨19,false⟩
    | 1 => .core 83 ⟨21,false⟩
    | 2 => .core 63 ⟨0,false⟩
    | _ => .boundary { kind := .unit 0 2, quiver := ⟨421,-1,-12,-207,35,-6⟩, returnVertex := 3 }

def q179Row79 : CoreRow 88 8 where
  quiver := ⟨2741,1,-9,299,43,1⟩
  word := [2,0,1,2,0,2,3]
  edges k := match k.val with
    | 0 => .core 87 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 2 3, quiver := ⟨-2741,819560,117854,-299,-43,1⟩, returnVertex := 1 }
    | 2 => .core 80 ⟨1,false⟩
    | _ => .core 66 ⟨0,false⟩

def q179Row80 : CoreRow 88 8 where
  quiver := ⟨2741,-8,-1,342,-299,1⟩
  word := [2,0,1,2,0,3,2]
  edges k := match k.val with
    | 0 => .mstrip 6 (0) 1 ⟨5,false⟩
    | 1 => .boundary { kind := .unit 0 3, quiver := ⟨-2741,937414,-1,-342,299,-102257⟩, returnVertex := 1 }
    | 2 => .core 67 ⟨0,false⟩
    | _ => .core 79 ⟨1,false⟩

def q179Row81 : CoreRow 88 8 where
  quiver := ⟨1,73,-7,9,6,508⟩
  word := [3,0,2,0,1,3,0]
  edges k := match k.val with
    | 0 => .core 69 ⟨0,false⟩
    | 1 => .mstrip 2 (0) 2 ⟨7,true⟩
    | 2 => .boundary { kind := .unit 0 1, quiver := ⟨1,-73,37077,-9,4578,-508⟩, returnVertex := 2 }
    | _ => .boundary { kind := .fork, quiver := ⟨-41,-3483,7,9,-6,-508⟩, returnVertex := 3 }

def q179Row82 : CoreRow 88 8 where
  quiver := ⟨1,-16,-6,-107,7,-747⟩
  word := [3,0,2,1,0,3,1]
  edges k := match k.val with
    | 0 => .mstrip 3 (0) 2 ⟨1,false⟩
    | 1 => .core 71 ⟨0,false⟩
    | 2 => .boundary { kind := .unit 0 1, quiver := ⟨1,16,-11958,107,-79922,747⟩, returnVertex := 2 }
    | _ => .boundary { kind := .fork, quiver := ⟨-41,-16,6,5122,-7,747⟩, returnVertex := 3 }

def q179Row83 : CoreRow 88 8 where
  quiver := ⟨-35,99,-12,-3,1,-2⟩
  word := [3,0,2,1,3,2,3,1,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 3, quiver := ⟨35,-99,12,3462,1,-1190⟩, returnVertex := 0 }
    | 1 => .core 78 ⟨21,false⟩
    | 2 => .boundary { kind := .fork, quiver := ⟨262,-99,-12,3,-5,2⟩, returnVertex := 2 }
    | _ => .mstrip 4 (0) 2 ⟨21,true⟩

def q179Row84 : CoreRow 88 8 where
  quiver := ⟨86,1,-1,794,-13,9⟩
  word := [0,1,0,1,0,2,0,3]
  edges k := match k.val with
    | 0 => .core 85 ⟨21,false⟩
    | 1 => .boundary { kind := .unit 0 3, quiver := ⟨-86,68285,-1,-794,13,-10313⟩, returnVertex := 1 }
    | 2 => .core 88 ⟨0,false⟩
    | _ => .core 74 ⟨0,false⟩

def q179Row85 : CoreRow 88 8 where
  quiver := ⟨99,-8,-1,794,86,1⟩
  word := [0,1,0,1,0,2,3,0]
  edges k := match k.val with
    | 0 => .core 75 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 2 3, quiver := ⟨-99,78598,8513,-794,-86,1⟩, returnVertex := 1 }
    | 2 => .mstrip 7 (0) 1 ⟨16,true⟩
    | _ => .core 84 ⟨21,false⟩

def q179Row86 : CoreRow 88 8 where
  quiver := ⟨53,1,-3,-11,146,2⟩
  word := [0,1,0,2,0,2,3,0]
  edges k := match k.val with
    | 0 => .core 76 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 0 2, quiver := ⟨-53,1,7735,11,-146,1608⟩, returnVertex := 1 }
    | 2 => .mstrip 5 (0) 2 ⟨13,true⟩
    | _ => .boundary { kind := .fork, quiver := ⟨-385,-5,3,-11,-146,-2⟩, returnVertex := 3 }

def q179Row87 : CoreRow 88 8 where
  quiver := ⟨-2741,-1,9,299,-24626,-8⟩
  word := [2,0,1,2,0,2,3,0]
  edges k := match k.val with
    | 0 => .core 79 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 0 2, quiver := ⟨2741,-1,-67499857,-299,24626,-7363182⟩, returnVertex := 1 }
    | 2 => .mstrip 6 (0) 2 ⟨13,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨218893,71,-9,299,24626,8⟩, returnVertex := 3 }

def q179Row88 : CoreRow 88 8 where
  quiver := ⟨86,-1,8,-794,7133,-9⟩
  word := [0,1,0,1,0,2,0,3,2]
  edges k := match k.val with
    | 0 => .mstrip 7 (0) 2 ⟨3,true⟩
    | 1 => .boundary { kind := .unit 0 2, quiver := ⟨-86,-1,613446,794,-7133,5663593⟩, returnVertex := 1 }
    | 2 => .core 84 ⟨0,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨86,71,-8,63403,-7133,9⟩, returnVertex := 3 }

def q179 : Certificate where
  initial := ⟨-2,-2,1,-1,-2,1⟩
  entryWord := []
  entryFrame := ⟨0,false⟩
  size := 88
  stripCount := 8
  core i := match i.val with
    | 0 => q179Row0
    | 1 => q179Row1
    | 2 => q179Row2
    | 3 => q179Row3
    | 4 => q179Row4
    | 5 => q179Row5
    | 6 => q179Row6
    | 7 => q179Row7
    | 8 => q179Row8
    | 9 => q179Row9
    | 10 => q179Row10
    | 11 => q179Row11
    | 12 => q179Row12
    | 13 => q179Row13
    | 14 => q179Row14
    | 15 => q179Row15
    | 16 => q179Row16
    | 17 => q179Row17
    | 18 => q179Row18
    | 19 => q179Row19
    | 20 => q179Row20
    | 21 => q179Row21
    | 22 => q179Row22
    | 23 => q179Row23
    | 24 => q179Row24
    | 25 => q179Row25
    | 26 => q179Row26
    | 27 => q179Row27
    | 28 => q179Row28
    | 29 => q179Row29
    | 30 => q179Row30
    | 31 => q179Row31
    | 32 => q179Row32
    | 33 => q179Row33
    | 34 => q179Row34
    | 35 => q179Row35
    | 36 => q179Row36
    | 37 => q179Row37
    | 38 => q179Row38
    | 39 => q179Row39
    | 40 => q179Row40
    | 41 => q179Row41
    | 42 => q179Row42
    | 43 => q179Row43
    | 44 => q179Row44
    | 45 => q179Row45
    | 46 => q179Row46
    | 47 => q179Row47
    | 48 => q179Row48
    | 49 => q179Row49
    | 50 => q179Row50
    | 51 => q179Row51
    | 52 => q179Row52
    | 53 => q179Row53
    | 54 => q179Row54
    | 55 => q179Row55
    | 56 => q179Row56
    | 57 => q179Row57
    | 58 => q179Row58
    | 59 => q179Row59
    | 60 => q179Row60
    | 61 => q179Row61
    | 62 => q179Row62
    | 63 => q179Row63
    | 64 => q179Row64
    | 65 => q179Row65
    | 66 => q179Row66
    | 67 => q179Row67
    | 68 => q179Row68
    | 69 => q179Row69
    | 70 => q179Row70
    | 71 => q179Row71
    | 72 => q179Row72
    | 73 => q179Row73
    | 74 => q179Row74
    | 75 => q179Row75
    | 76 => q179Row76
    | 77 => q179Row77
    | 78 => q179Row78
    | 79 => q179Row79
    | 80 => q179Row80
    | 81 => q179Row81
    | 82 => q179Row82
    | 83 => q179Row83
    | 84 => q179Row84
    | 85 => q179Row85
    | 86 => q179Row86
    | 87 => q179Row87
    | _ => q179Row88
  strips i := match i.val with
    | 0 => q179Strip0
    | 1 => q179Strip1
    | 2 => q179Strip2
    | 3 => q179Strip3
    | 4 => q179Strip4
    | 5 => q179Strip5
    | 6 => q179Strip6
    | _ => q179Strip7
  triangleAvoidance := true

def q455Strip0 : StripRecord 12 where
  m := (3)
  a := (50)
  b := (10)
  c := (16)
  rootCore := 11
  rootQuiver := ⟨-16,1,3,-10,-50,1⟩
  rootWord := [1,0,3,2,0]
  rootFrame := ⟨22,false⟩
  backward p := match p.val with
    | 0 => ⟨10,⟨11,false⟩⟩
    | 1 => ⟨9,⟨17,false⟩⟩
    | _ => ⟨12,⟨5,false⟩⟩

def q455Row0 : CoreRow 12 1 where
  quiver := ⟨-2,-1,1,0,-2,1⟩
  word := []
  edges k := match k.val with
    | 0 => .core 1 ⟨0,false⟩
    | 1 => .core 2 ⟨0,false⟩
    | 2 => .core 0 ⟨21,true⟩
    | _ => .core 0 ⟨14,true⟩

def q455Row1 : CoreRow 12 1 where
  quiver := ⟨2,1,-1,0,0,2⟩
  word := [0]
  edges k := match k.val with
    | 0 => .core 0 ⟨0,false⟩
    | 1 => .core 1 ⟨1,true⟩
    | 2 => .core 1 ⟨1,false⟩
    | _ => .core 1 ⟨1,false⟩

def q455Row2 : CoreRow 12 1 where
  quiver := ⟨2,-1,-3,0,2,1⟩
  word := [1]
  edges k := match k.val with
    | 0 => .core 3 ⟨0,false⟩
    | 1 => .core 0 ⟨0,false⟩
    | 2 => .core 2 ⟨21,true⟩
    | _ => .core 4 ⟨0,false⟩

def q455Row3 : CoreRow 12 1 where
  quiver := ⟨-2,1,3,-2,-4,1⟩
  word := [1,0]
  edges k := match k.val with
    | 0 => .core 2 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 2 3, quiver := ⟨2,-3,-5,2,4,1⟩, returnVertex := 1 }
    | 2 => .core 5 ⟨0,false⟩
    | _ => .core 6 ⟨0,false⟩

def q455Row4 : CoreRow 12 1 where
  quiver := ⟨-4,-4,3,0,-2,-1⟩
  word := [1,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .diamond 1 2, quiver := ⟨4,4,-3,0,10,11⟩, returnVertex := 0 }
    | 1 => .zero (2) (4) (4) (5) { phase := 0, returnVertex := 1, frame := ⟨14,true⟩, alternateTarget := 5, alternateFrame := ⟨15,true⟩ }
    | 2 => .core 5 ⟨15,true⟩
    | _ => .core 2 ⟨0,false⟩

def q455Row5 : CoreRow 12 1 where
  quiver := ⟨0,-1,4,2,-4,-1⟩
  word := [1,0,2]
  edges k := match k.val with
    | 0 => .core 4 ⟨20,true⟩
    | 1 => .zero (2) (4) (4) (5) { phase := 1, returnVertex := 1, frame := ⟨1,false⟩, alternateTarget := 4, alternateFrame := ⟨20,true⟩ }
    | 2 => .core 3 ⟨0,false⟩
    | _ => .core 7 ⟨0,false⟩

def q455Row6 : CoreRow 12 1 where
  quiver := ⟨10,1,-3,-6,4,-1⟩
  word := [1,0,3]
  edges k := match k.val with
    | 0 => .core 8 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 0 2, quiver := ⟨-10,1,37,6,-4,23⟩, returnVertex := 1 }
    | 2 => .core 9 ⟨0,false⟩
    | _ => .core 3 ⟨0,false⟩

def q455Row7 : CoreRow 12 1 where
  quiver := ⟨16,3,-4,2,4,1⟩
  word := [1,0,2,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨-16,-3,4,2,-60,-11⟩, returnVertex := 0 }
    | 1 => .boundary { kind := .unit 2 3, quiver := ⟨-16,35,60,-2,-4,1⟩, returnVertex := 1 }
    | 2 => .core 9 ⟨1,false⟩
    | _ => .core 5 ⟨0,false⟩

def q455Row8 : CoreRow 12 1 where
  quiver := ⟨-10,-1,3,-6,-26,-4⟩
  word := [1,0,3,0]
  edges k := match k.val with
    | 0 => .core 6 ⟨0,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨10,-61,-257,6,26,-4⟩, returnVertex := 1 }
    | 2 => .core 10 ⟨0,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨68,11,-3,-6,26,4⟩, returnVertex := 3 }

def q455Row9 : CoreRow 12 1 where
  quiver := ⟨16,-1,-3,6,-2,1⟩
  word := [1,0,3,2]
  edges k := match k.val with
    | 0 => .core 11 ⟨0,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨-16,95,-3,-6,2,-11⟩, returnVertex := 1 }
    | 2 => .core 6 ⟨0,false⟩
    | _ => .core 7 ⟨1,false⟩

def q455Row10 : CoreRow 12 1 where
  quiver := ⟨-10,1,-1,6,-50,4⟩
  word := [1,0,3,0,2]
  edges k := match k.val with
    | 0 => .core 11 ⟨14,false⟩
    | 1 => .boundary { kind := .unit 0 2, quiver := ⟨10,1,-501,-6,50,-296⟩, returnVertex := 1 }
    | 2 => .core 8 ⟨0,false⟩
    | _ => .core 12 ⟨0,false⟩

def q455Row11 : CoreRow 12 1 where
  quiver := ⟨-16,1,3,-10,-50,1⟩
  word := [1,0,3,2,0]
  edges k := match k.val with
    | 0 => .core 9 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 2 3, quiver := ⟨16,-159,-797,10,50,1⟩, returnVertex := 1 }
    | 2 => .core 10 ⟨14,false⟩
    | _ => .mstrip 0 (0) 1 ⟨22,false⟩

def q455Row12 : CoreRow 12 1 where
  quiver := ⟨-10,-3,1,-194,50,-4⟩
  word := [1,0,3,0,2,3]
  edges k := match k.val with
    | 0 => .mstrip 0 (0) 2 ⟨5,false⟩
    | 1 => .boundary { kind := .unit 0 3, quiver := ⟨10,-1943,1,194,-50,9696⟩, returnVertex := 1 }
    | 2 => .boundary { kind := .fork, quiver := ⟨-10,3,-11,194,-726,4⟩, returnVertex := 2 }
    | _ => .core 10 ⟨0,false⟩

def q455 : Certificate where
  initial := ⟨-2,-1,1,0,-2,1⟩
  entryWord := []
  entryFrame := ⟨0,false⟩
  size := 12
  stripCount := 1
  core i := match i.val with
    | 0 => q455Row0
    | 1 => q455Row1
    | 2 => q455Row2
    | 3 => q455Row3
    | 4 => q455Row4
    | 5 => q455Row5
    | 6 => q455Row6
    | 7 => q455Row7
    | 8 => q455Row8
    | 9 => q455Row9
    | 10 => q455Row10
    | 11 => q455Row11
    | _ => q455Row12
  strips i := match i.val with
    | _ => q455Strip0
  triangleAvoidance := true

def q511Strip0 : StripRecord 26 where
  m := (2)
  a := (20)
  b := (6)
  c := (10)
  rootCore := 13
  rootQuiver := ⟨2,1,-10,-1,20,6⟩
  rootWord := [0,1,2,0]
  rootFrame := ⟨8,false⟩
  backward p := match p.val with
    | 0 => ⟨12,⟨6,false⟩⟩
    | 1 => ⟨7,⟨12,false⟩⟩
    | _ => ⟨18,⟨0,false⟩⟩

def q511Strip1 : StripRecord 26 where
  m := (5)
  a := (40)
  b := (6)
  c := (8)
  rootCore := 21
  rootQuiver := ⟨-1,1,6,5,-8,40⟩
  rootWord := [0,3,0,2,1]
  rootFrame := ⟨12,false⟩
  backward p := match p.val with
    | 0 => ⟨23,⟨0,false⟩⟩
    | 1 => ⟨16,⟨8,false⟩⟩
    | _ => ⟨25,⟨8,false⟩⟩

def q511Strip2 : StripRecord 26 where
  m := (5)
  a := (110)
  b := (18)
  c := (22)
  rootCore := 22
  rootQuiver := ⟨-1,-5,22,-1,-18,-110⟩
  rootWord := [0,3,1,2,0]
  rootFrame := ⟨14,true⟩
  backward p := match p.val with
    | 0 => ⟨24,⟨6,true⟩⟩
    | 1 => ⟨17,⟨14,true⟩⟩
    | _ => ⟨26,⟨14,true⟩⟩

def q511Row0 : CoreRow 26 3 where
  quiver := ⟨-2,-1,2,-1,0,-2⟩
  word := []
  edges k := match k.val with
    | 0 => .core 1 ⟨0,false⟩
    | 1 => .core 2 ⟨0,false⟩
    | 2 => .core 0 ⟨6,true⟩
    | _ => .core 2 ⟨0,true⟩

def q511Row1 : CoreRow 26 3 where
  quiver := ⟨2,1,-2,-1,4,0⟩
  word := [0]
  edges k := match k.val with
    | 0 => .core 0 ⟨0,false⟩
    | 1 => .core 3 ⟨0,false⟩
    | 2 => .core 4 ⟨0,false⟩
    | _ => .core 5 ⟨0,false⟩

def q511Row2 : CoreRow 26 3 where
  quiver := ⟨2,-3,2,1,0,-2⟩
  word := [1]
  edges k := match k.val with
    | 0 => .boundary { kind := .diamond 1 3, quiver := ⟨-2,3,-2,-5,0,4⟩, returnVertex := 0 }
    | 1 => .core 0 ⟨0,false⟩
    | 2 => .core 4 ⟨12,true⟩
    | _ => .core 0 ⟨0,true⟩

def q511Row3 : CoreRow 26 3 where
  quiver := ⟨-2,1,6,1,-4,4⟩
  word := [0,1]
  edges k := match k.val with
    | 0 => .core 6 ⟨0,false⟩
    | 1 => .core 1 ⟨0,false⟩
    | 2 => .core 7 ⟨0,false⟩
    | _ => .boundary { kind := .unit 0 2, quiver := ⟨22,1,-6,-15,4,-4⟩, returnVertex := 3 }

def q511Row4 : CoreRow 26 3 where
  quiver := ⟨3,-1,-2,1,4,0⟩
  word := [0,2]
  edges k := match k.val with
    | 0 => .core 2 ⟨8,true⟩
    | 1 => .core 8 ⟨0,false⟩
    | 2 => .core 1 ⟨0,false⟩
    | _ => .core 9 ⟨0,false⟩

def q511Row5 : CoreRow 26 3 where
  quiver := ⟨-6,1,2,-1,-4,0⟩
  word := [0,3]
  edges k := match k.val with
    | 0 => .core 10 ⟨0,false⟩
    | 1 => .core 11 ⟨0,false⟩
    | 2 => .core 9 ⟨0,false⟩
    | _ => .core 1 ⟨0,false⟩

def q511Row6 : CoreRow 26 3 where
  quiver := ⟨2,-1,-6,3,8,4⟩
  word := [0,1,0]
  edges k := match k.val with
    | 0 => .core 3 ⟨0,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨-2,5,10,-3,-8,4⟩, returnVertex := 1 }
    | 2 => .core 12 ⟨0,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨-46,-25,6,3,-8,-4⟩, returnVertex := 3 }

def q511Row7 : CoreRow 26 3 where
  quiver := ⟨-2,-1,10,-1,0,-4⟩
  word := [0,1,2]
  edges k := match k.val with
    | 0 => .core 13 ⟨0,false⟩
    | 1 => .core 8 ⟨2,false⟩
    | 2 => .core 3 ⟨0,false⟩
    | _ => .zero (4) (2) (10) (37) { phase := 1, returnVertex := 3, frame := ⟨10,false⟩, alternateTarget := 8, alternateFrame := ⟨2,false⟩ }

def q511Row8 : CoreRow 26 3 where
  quiver := ⟨-3,2,10,-1,-4,0⟩
  word := [0,2,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .diamond 2 3, quiver := ⟨3,-2,-10,5,26,0⟩, returnVertex := 0 }
    | 1 => .core 4 ⟨0,false⟩
    | 2 => .core 7 ⟨2,false⟩
    | _ => .zero (4) (2) (10) (37) { phase := 0, returnVertex := 3, frame := ⟨16,false⟩, alternateTarget := 7, alternateFrame := ⟨2,false⟩ }

def q511Row9 : CoreRow 26 3 where
  quiver := ⟨-5,-1,2,1,-4,0⟩
  word := [0,2,3]
  edges k := match k.val with
    | 0 => .core 14 ⟨0,false⟩
    | 1 => .core 15 ⟨0,false⟩
    | 2 => .core 5 ⟨0,false⟩
    | _ => .core 4 ⟨0,false⟩

def q511Row10 : CoreRow 26 3 where
  quiver := ⟨6,-1,-2,5,8,0⟩
  word := [0,3,0]
  edges k := match k.val with
    | 0 => .core 5 ⟨0,false⟩
    | 1 => .boundary { kind := .diamond 2 3, quiver := ⟨-6,29,46,-5,-8,0⟩, returnVertex := 1 }
    | 2 => .core 16 ⟨0,false⟩
    | _ => .zero (2) (5) (8) (10) { phase := 0, returnVertex := 3, frame := ⟨17,false⟩, alternateTarget := 16, alternateFrame := ⟨0,false⟩ }

def q511Row11 : CoreRow 26 3 where
  quiver := ⟨6,-5,-22,1,4,0⟩
  word := [0,3,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .diamond 2 3, quiver := ⟨-6,5,22,-29,-128,0⟩, returnVertex := 0 }
    | 1 => .core 5 ⟨0,false⟩
    | 2 => .core 17 ⟨0,false⟩
    | _ => .zero (4) (5) (22) (82) { phase := 0, returnVertex := 3, frame := ⟨16,true⟩, alternateTarget := 17, alternateFrame := ⟨0,false⟩ }

def q511Row12 : CoreRow 26 3 where
  quiver := ⟨-1,1,-6,-3,20,-4⟩
  word := [0,1,0,2]
  edges k := match k.val with
    | 0 => .core 13 ⟨14,false⟩
    | 1 => .core 18 ⟨0,false⟩
    | 2 => .core 6 ⟨0,false⟩
    | _ => .boundary { kind := .unit 0 2, quiver := ⟨-121,1,6,77,-20,4⟩, returnVertex := 3 }

def q511Row13 : CoreRow 26 3 where
  quiver := ⟨2,1,-10,-1,20,6⟩
  word := [0,1,2,0]
  edges k := match k.val with
    | 0 => .core 7 ⟨0,false⟩
    | 1 => .mstrip 0 (0) 1 ⟨8,false⟩
    | 2 => .core 12 ⟨14,false⟩
    | _ => .boundary { kind := .unit 1 2, quiver := ⟨-198,-59,10,-1,-20,-6⟩, returnVertex := 3 }

def q511Row14 : CoreRow 26 3 where
  quiver := ⟨5,1,-2,1,6,2⟩
  word := [0,2,3,0]
  edges k := match k.val with
    | 0 => .core 9 ⟨0,false⟩
    | 1 => .core 19 ⟨0,false⟩
    | 2 => .core 16 ⟨14,false⟩
    | _ => .boundary { kind := .unit 1 2, quiver := ⟨-7,-3,2,1,-6,-2⟩, returnVertex := 3 }

def q511Row15 : CoreRow 26 3 where
  quiver := ⟨5,-1,-18,-1,4,-4⟩
  word := [0,2,3,1]
  edges k := match k.val with
    | 0 => .core 20 ⟨0,false⟩
    | 1 => .core 9 ⟨0,false⟩
    | 2 => .core 17 ⟨2,false⟩
    | _ => .boundary { kind := .unit 0 2, quiver := ⟨-67,-1,18,15,-4,4⟩, returnVertex := 3 }

def q511Row16 : CoreRow 26 3 where
  quiver := ⟨1,1,-2,-5,8,0⟩
  word := [0,3,0,2]
  edges k := match k.val with
    | 0 => .core 14 ⟨14,false⟩
    | 1 => .core 21 ⟨0,false⟩
    | 2 => .core 10 ⟨0,false⟩
    | _ => .zero (2) (5) (8) (10) { phase := 1, returnVertex := 3, frame := ⟨17,false⟩, alternateTarget := 10, alternateFrame := ⟨0,false⟩ }

def q511Row17 : CoreRow 26 3 where
  quiver := ⟨1,5,-22,-1,4,0⟩
  word := [0,3,1,2]
  edges k := match k.val with
    | 0 => .core 22 ⟨0,false⟩
    | 1 => .core 15 ⟨2,false⟩
    | 2 => .core 11 ⟨0,false⟩
    | _ => .zero (4) (5) (22) (82) { phase := 1, returnVertex := 3, frame := ⟨16,true⟩, alternateTarget := 11, alternateFrame := ⟨0,false⟩ }

def q511Row18 : CoreRow 26 3 where
  quiver := ⟨1,-2,-6,3,-20,56⟩
  word := [0,1,0,2,1]
  edges k := match k.val with
    | 0 => .mstrip 0 (0) 2 ⟨0,false⟩
    | 1 => .core 12 ⟨0,false⟩
    | 2 => .boundary { kind := .fork, quiver := ⟨-5,2,-6,-3,148,-56⟩, returnVertex := 2 }
    | _ => .boundary { kind := .unit 0 1, quiver := ⟨1,-338,6,-1117,20,-56⟩, returnVertex := 3 }

def q511Row19 : CoreRow 26 3 where
  quiver := ⟨-5,6,28,-1,-6,2⟩
  word := [0,2,3,0,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨5,-6,-28,29,134,2⟩, returnVertex := 0 }
    | 1 => .core 14 ⟨0,false⟩
    | 2 => .core 23 ⟨0,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨163,6,-28,-13,6,-2⟩, returnVertex := 3 }

def q511Row20 : CoreRow 26 3 where
  quiver := ⟨-5,1,18,-6,-86,-4⟩
  word := [0,2,3,1,0]
  edges k := match k.val with
    | 0 => .core 15 ⟨0,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨5,-29,-412,6,86,-4⟩, returnVertex := 1 }
    | 2 => .core 24 ⟨0,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨1543,73,-18,-6,86,4⟩, returnVertex := 3 }

def q511Row21 : CoreRow 26 3 where
  quiver := ⟨-1,1,6,5,-8,40⟩
  word := [0,3,0,2,1]
  edges k := match k.val with
    | 0 => .core 23 ⟨12,false⟩
    | 1 => .core 16 ⟨0,false⟩
    | 2 => .mstrip 1 (0) 1 ⟨12,false⟩
    | _ => .boundary { kind := .unit 0 2, quiver := ⟨47,1,-6,-315,8,-40⟩, returnVertex := 3 }

def q511Row22 : CoreRow 26 3 where
  quiver := ⟨-1,-5,22,-1,-18,-110⟩
  word := [0,3,1,2,0]
  edges k := match k.val with
    | 0 => .core 17 ⟨0,false⟩
    | 1 => .core 24 ⟨8,false⟩
    | 2 => .mstrip 2 (0) 1 ⟨14,true⟩
    | _ => .boundary { kind := .unit 1 2, quiver := ⟨395,2415,-22,-1,18,110⟩, returnVertex := 3 }

def q511Row23 : CoreRow 26 3 where
  quiver := ⟨1,-6,40,1,-6,-2⟩
  word := [0,2,3,0,1,2]
  edges k := match k.val with
    | 0 => .core 25 ⟨2,false⟩
    | 1 => .core 21 ⟨8,false⟩
    | 2 => .core 19 ⟨0,false⟩
    | _ => .boundary { kind := .unit 1 2, quiver := ⟨241,74,-40,1,6,2⟩, returnVertex := 3 }

def q511Row24 : CoreRow 26 3 where
  quiver := ⟨1,-1,18,6,-110,4⟩
  word := [0,2,3,1,0,2]
  edges k := match k.val with
    | 0 => .core 22 ⟨12,false⟩
    | 1 => .core 26 ⟨14,false⟩
    | 2 => .core 20 ⟨0,false⟩
    | _ => .boundary { kind := .unit 0 2, quiver := ⟨1981,-1,-18,-434,110,-4⟩, returnVertex := 3 }

def q511Row25 : CoreRow 26 3 where
  quiver := ⟨6,-1,-40,5,238,-6⟩
  word := [0,3,0,2,1,2,0,2]
  edges k := match k.val with
    | 0 => .core 23 ⟨2,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨-6,29,1388,-5,-238,-6⟩, returnVertex := 1 }
    | 2 => .mstrip 1 (0) 2 ⟨12,false⟩
    | _ => .boundary { kind := .unit 0 2, quiver := ⟨-9514,-1,40,1433,-238,6⟩, returnVertex := 3 }

def q511Row26 : CoreRow 26 3 where
  quiver := ⟨6,-5,-656,1,110,18⟩
  word := [0,3,1,2,0,2,1,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨-6,5,656,-29,-3826,18⟩, returnVertex := 0 }
    | 1 => .core 24 ⟨14,false⟩
    | 2 => .mstrip 2 (0) 2 ⟨14,true⟩
    | _ => .boundary { kind := .unit 1 2, quiver := ⟨-72154,-11813,656,1,-110,-18⟩, returnVertex := 3 }

def q511 : Certificate where
  initial := ⟨-2,-1,2,-1,0,-2⟩
  entryWord := []
  entryFrame := ⟨0,false⟩
  size := 26
  stripCount := 3
  core i := match i.val with
    | 0 => q511Row0
    | 1 => q511Row1
    | 2 => q511Row2
    | 3 => q511Row3
    | 4 => q511Row4
    | 5 => q511Row5
    | 6 => q511Row6
    | 7 => q511Row7
    | 8 => q511Row8
    | 9 => q511Row9
    | 10 => q511Row10
    | 11 => q511Row11
    | 12 => q511Row12
    | 13 => q511Row13
    | 14 => q511Row14
    | 15 => q511Row15
    | 16 => q511Row16
    | 17 => q511Row17
    | 18 => q511Row18
    | 19 => q511Row19
    | 20 => q511Row20
    | 21 => q511Row21
    | 22 => q511Row22
    | 23 => q511Row23
    | 24 => q511Row24
    | 25 => q511Row25
    | _ => q511Row26
  strips i := match i.val with
    | 0 => q511Strip0
    | 1 => q511Strip1
    | _ => q511Strip2
  triangleAvoidance := true

end QuiverProofs.BoundedLStarData
