import QuiverProofs.LStarSyntax

/-! Exact normalized E1/E4 source data. This module contains no
acceptance or NMA assertion. All mathematical obligations are
checked separately in PrintedLStarCompletion. -/
namespace QuiverProofs.PrintedLStarData
open LStar

def e1Row0 : CoreRow 16 0 where
  quiver := ⟨-2,-2,1,-1,2,-2⟩
  word := []
  edges k := match k.val with
    | 0 => .core 1 ⟨0,false⟩
    | 1 => .core 1 ⟨7,true⟩
    | 2 => .core 2 ⟨0,false⟩
    | _ => .core 2 ⟨7,true⟩

def e1Row1 : CoreRow 16 0 where
  quiver := ⟨2,2,-1,-1,4,0⟩
  word := [0]
  edges k := match k.val with
    | 0 => .core 0 ⟨0,false⟩
    | 1 => .core 3 ⟨0,false⟩
    | 2 => .core 4 ⟨0,false⟩
    | _ => .core 5 ⟨0,false⟩

def e1Row2 : CoreRow 16 0 where
  quiver := ⟨-2,2,-3,1,0,2⟩
  word := [2]
  edges k := match k.val with
    | 0 => .boundary { kind := .diamond 1 3, quiver := ⟨2,-2,3,5,0,-4⟩, returnVertex := 0 }
    | 1 => .core 6 ⟨0,false⟩
    | 2 => .core 0 ⟨0,false⟩
    | _ => .core 7 ⟨0,false⟩

def e1Row3 : CoreRow 16 0 where
  quiver := ⟨-2,2,7,1,-4,4⟩
  word := [0,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨2,-2,-7,5,10,4⟩, returnVertex := 0 }
    | 1 => .core 1 ⟨0,false⟩
    | 2 => .core 8 ⟨0,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨26,2,-7,-15,4,-4⟩, returnVertex := 3 }

def e1Row4 : CoreRow 16 0 where
  quiver := ⟨4,-2,-1,1,4,0⟩
  word := [0,2]
  edges k := match k.val with
    | 0 => .core 9 ⟨0,false⟩
    | 1 => .core 10 ⟨0,false⟩
    | 2 => .core 1 ⟨0,false⟩
    | _ => .core 11 ⟨0,false⟩

def e1Row5 : CoreRow 16 0 where
  quiver := ⟨-2,2,1,-1,-4,0⟩
  word := [0,3]
  edges k := match k.val with
    | 0 => .core 6 ⟨10,true⟩
    | 1 => .core 12 ⟨0,false⟩
    | 2 => .core 11 ⟨0,false⟩
    | _ => .core 1 ⟨0,false⟩

def e1Row6 : CoreRow 16 0 where
  quiver := ⟨2,2,-3,-1,0,2⟩
  word := [2,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 2, quiver := ⟨-2,-2,3,-1,-6,-4⟩, returnVertex := 0 }
    | 1 => .core 2 ⟨0,false⟩
    | 2 => .core 5 ⟨13,true⟩
    | _ => .core 13 ⟨0,false⟩

def e1Row7 : CoreRow 16 0 where
  quiver := ⟨-2,-4,3,1,0,-2⟩
  word := [2,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 2, quiver := ⟨2,4,-3,1,6,10⟩, returnVertex := 0 }
    | 1 => .core 13 ⟨0,false⟩
    | 2 => .core 14 ⟨0,false⟩
    | _ => .core 2 ⟨0,false⟩

def e1Row8 : CoreRow 16 0 where
  quiver := ⟨-2,-2,15,-1,0,-4⟩
  word := [0,1,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 2, quiver := ⟨2,2,-15,-1,30,26⟩, returnVertex := 0 }
    | 1 => .core 10 ⟨2,false⟩
    | 2 => .core 3 ⟨0,false⟩
    | _ => .zero (4) (2) (15) (56) { phase := 1, returnVertex := 3, frame := ⟨10,false⟩, alternateTarget := 10, alternateFrame := ⟨2,false⟩ }

def e1Row9 : CoreRow 16 0 where
  quiver := ⟨-4,2,1,-7,0,0⟩
  word := [0,2,0]
  edges k := match k.val with
    | 0 => .core 4 ⟨0,false⟩
    | 1 => .pendant (7) (4) (26) { phase := 1, returnVertex := 1, frame := ⟨21,false⟩, alternateTarget := 12, alternateFrame := ⟨13,true⟩ }
    | 2 => .pendant (7) (2) (10) { phase := 0, returnVertex := 2, frame := ⟨23,true⟩, alternateTarget := 12, alternateFrame := ⟨13,true⟩ }
    | _ => .core 12 ⟨13,true⟩

def e1Row10 : CoreRow 16 0 where
  quiver := ⟨-4,2,15,-1,-4,0⟩
  word := [0,2,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .diamond 2 3, quiver := ⟨4,-2,-15,7,56,0⟩, returnVertex := 0 }
    | 1 => .core 4 ⟨0,false⟩
    | 2 => .core 8 ⟨2,false⟩
    | _ => .zero (4) (2) (15) (56) { phase := 0, returnVertex := 3, frame := ⟨16,false⟩, alternateTarget := 8, alternateFrame := ⟨2,false⟩ }

def e1Row11 : CoreRow 16 0 where
  quiver := ⟨0,-2,1,1,-4,0⟩
  word := [0,2,3]
  edges k := match k.val with
    | 0 => .core 5 ⟨16,true⟩
    | 1 => .core 4 ⟨16,true⟩
    | 2 => .core 5 ⟨0,false⟩
    | _ => .core 4 ⟨0,false⟩

def e1Row12 : CoreRow 16 0 where
  quiver := ⟨2,0,-7,1,4,0⟩
  word := [0,3,1]
  edges k := match k.val with
    | 0 => .pendant (7) (2) (10) { phase := 1, returnVertex := 0, frame := ⟨13,false⟩, alternateTarget := 9, alternateFrame := ⟨10,true⟩ }
    | 1 => .core 5 ⟨0,false⟩
    | 2 => .core 9 ⟨10,true⟩
    | _ => .pendant (7) (4) (26) { phase := 0, returnVertex := 3, frame := ⟨16,true⟩, alternateTarget := 9, alternateFrame := ⟨10,true⟩ }

def e1Row13 : CoreRow 16 0 where
  quiver := ⟨2,-4,3,-1,0,-2⟩
  word := [2,1,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .diamond 1 3, quiver := ⟨-2,4,-3,-9,0,10⟩, returnVertex := 0 }
    | 1 => .core 7 ⟨0,false⟩
    | 2 => .core 15 ⟨0,false⟩
    | _ => .core 6 ⟨0,false⟩

def e1Row14 : CoreRow 16 0 where
  quiver := ⟨-6,4,-5,-1,0,2⟩
  word := [2,3,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .diamond 1 3, quiver := ⟨6,-4,5,23,0,-18⟩, returnVertex := 0 }
    | 1 => .core 16 ⟨0,false⟩
    | 2 => .core 7 ⟨0,false⟩
    | _ => .zero (2) (6) (5) (6) { phase := 0, returnVertex := 3, frame := ⟨10,true⟩, alternateTarget := 16, alternateFrame := ⟨0,false⟩ }

def e1Row15 : CoreRow 16 0 where
  quiver := ⟨2,4,-5,1,-2,2⟩
  word := [2,1,3,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 2, quiver := ⟨-2,-4,5,1,-12,-18⟩, returnVertex := 0 }
    | 1 => .core 16 ⟨2,false⟩
    | 2 => .core 13 ⟨0,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨2,-6,5,-3,2,-2⟩, returnVertex := 3 }

def e1Row16 : CoreRow 16 0 where
  quiver := ⟨6,-2,-5,1,0,2⟩
  word := [2,3,2,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨-6,2,5,-11,-30,2⟩, returnVertex := 0 }
    | 1 => .core 14 ⟨0,false⟩
    | 2 => .core 15 ⟨2,false⟩
    | _ => .zero (2) (6) (5) (6) { phase := 1, returnVertex := 3, frame := ⟨10,true⟩, alternateTarget := 14, alternateFrame := ⟨0,false⟩ }

def e1 : Certificate where
  initial := ⟨-2,-2,1,-1,2,-2⟩
  entryWord := []
  entryFrame := ⟨0,false⟩
  size := 16
  stripCount := 0
  core i := match i.val with
    | 0 => e1Row0
    | 1 => e1Row1
    | 2 => e1Row2
    | 3 => e1Row3
    | 4 => e1Row4
    | 5 => e1Row5
    | 6 => e1Row6
    | 7 => e1Row7
    | 8 => e1Row8
    | 9 => e1Row9
    | 10 => e1Row10
    | 11 => e1Row11
    | 12 => e1Row12
    | 13 => e1Row13
    | 14 => e1Row14
    | 15 => e1Row15
    | _ => e1Row16
  strips := Fin.elim0
  triangleAvoidance := true

def e4Row0 : CoreRow 4 0 where
  quiver := ⟨-2,-1,2,-2,-1,-2⟩
  word := []
  edges k := match k.val with
    | 0 => .core 1 ⟨0,false⟩
    | 1 => .core 2 ⟨0,false⟩
    | 2 => .core 2 ⟨23,true⟩
    | _ => .core 1 ⟨23,true⟩

def e4Row1 : CoreRow 4 0 where
  quiver := ⟨2,1,-2,-2,3,0⟩
  word := [0]
  edges k := match k.val with
    | 0 => .core 0 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 0 2, quiver := ⟨-2,1,4,2,-3,6⟩, returnVertex := 1 }
    | 2 => .core 3 ⟨0,false⟩
    | _ => .core 3 ⟨0,true⟩

def e4Row2 : CoreRow 4 0 where
  quiver := ⟨2,-5,0,2,1,-2⟩
  word := [1]
  edges k := match k.val with
    | 0 => .zero (2) (2) (5) (6) { phase := 1, returnVertex := 0, frame := ⟨19,false⟩, alternateTarget := 4, alternateFrame := ⟨0,false⟩ }
    | 1 => .core 0 ⟨0,false⟩
    | 2 => .boundary { kind := .unit 1 3, quiver := ⟨-8,5,-10,-2,1,2⟩, returnVertex := 2 }
    | _ => .core 4 ⟨0,false⟩

def e4Row3 : CoreRow 4 0 where
  quiver := ⟨4,-1,-2,2,3,0⟩
  word := [0,2]
  edges k := match k.val with
    | 0 => .core 4 ⟨18,true⟩
    | 1 => .boundary { kind := .diamond 2 3, quiver := ⟨-4,7,10,-2,-3,0⟩, returnVertex := 1 }
    | 2 => .core 1 ⟨0,false⟩
    | _ => .core 1 ⟨0,true⟩

def e4Row4 : CoreRow 4 0 where
  quiver := ⟨2,-5,0,4,-1,2⟩
  word := [1,3]
  edges k := match k.val with
    | 0 => .zero (2) (2) (5) (6) { phase := 0, returnVertex := 0, frame := ⟨19,false⟩, alternateTarget := 2, alternateFrame := ⟨0,false⟩ }
    | 1 => .core 3 ⟨9,true⟩
    | 2 => .boundary { kind := .diamond 0 3, quiver := ⟨-18,5,0,-4,7,-2⟩, returnVertex := 2 }
    | _ => .core 2 ⟨0,false⟩

def e4 : Certificate where
  initial := ⟨-2,-1,2,-2,-1,-2⟩
  entryWord := []
  entryFrame := ⟨0,false⟩
  size := 4
  stripCount := 0
  core i := match i.val with
    | 0 => e4Row0
    | 1 => e4Row1
    | 2 => e4Row2
    | 3 => e4Row3
    | _ => e4Row4
  strips := Fin.elim0
  triangleAvoidance := true

end QuiverProofs.PrintedLStarData
