import QuiverProofs.LStarSyntax

/-! Exact finite records for the four printed witnesses.
This generated module asserts no acceptance or NMA result;
the shared LStar checker verifies all mathematical obligations. -/
namespace QuiverProofs.WitnessLStarData
open LStar

def delayedRow0 : CoreRow 57 4 where
  quiver := ⟨0,-1,3,-2,-2,-2⟩
  word := []
  edges k := match k.val with
    | 0 => .core 1 ⟨0,false⟩
    | 1 => .core 2 ⟨0,false⟩
    | 2 => .core 3 ⟨0,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨6,5,-3,-2,2,2⟩, returnVertex := 3 }

def delayedRow1 : CoreRow 57 4 where
  quiver := ⟨0,1,-3,-2,-2,1⟩
  word := [0]
  edges k := match k.val with
    | 0 => .core 0 ⟨0,false⟩
    | 1 => .core 4 ⟨0,false⟩
    | 2 => .core 5 ⟨0,false⟩
    | _ => .core 6 ⟨0,false⟩

def delayedRow2 : CoreRow 57 4 where
  quiver := ⟨0,-1,3,2,2,-2⟩
  word := [1]
  edges k := match k.val with
    | 0 => .core 4 ⟨0,false⟩
    | 1 => .core 0 ⟨0,false⟩
    | 2 => .core 7 ⟨0,false⟩
    | _ => .boundary { kind := .diamond 0 1, quiver := ⟨0,5,-3,6,-2,2⟩, returnVertex := 3 }

def delayedRow3 : CoreRow 57 4 where
  quiver := ⟨0,1,1,2,-6,2⟩
  word := [2]
  edges k := match k.val with
    | 0 => .core 8 ⟨0,false⟩
    | 1 => .core 9 ⟨0,false⟩
    | 2 => .core 0 ⟨0,false⟩
    | _ => .core 10 ⟨0,false⟩

def delayedRow4 : CoreRow 57 4 where
  quiver := ⟨0,1,-3,2,2,1⟩
  word := [0,1]
  edges k := match k.val with
    | 0 => .core 2 ⟨0,false⟩
    | 1 => .core 1 ⟨0,false⟩
    | 2 => .core 11 ⟨0,false⟩
    | _ => .core 12 ⟨0,false⟩

def delayedRow5 : CoreRow 57 4 where
  quiver := ⟨2,-1,-2,2,-2,-1⟩
  word := [0,2]
  edges k := match k.val with
    | 0 => .core 8 ⟨14,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨-2,3,-2,-2,2,-5⟩, returnVertex := 1 }
    | 2 => .core 1 ⟨0,false⟩
    | _ => .core 7 ⟨14,false⟩

def delayedRow6 : CoreRow 57 4 where
  quiver := ⟨0,-2,3,-4,2,-1⟩
  word := [0,3]
  edges k := match k.val with
    | 0 => .core 13 ⟨0,false⟩
    | 1 => .core 14 ⟨0,false⟩
    | 2 => .core 15 ⟨0,false⟩
    | _ => .core 1 ⟨0,false⟩

def delayedRow7 : CoreRow 57 4 where
  quiver := ⟨-2,1,1,-2,2,2⟩
  word := [1,2]
  edges k := match k.val with
    | 0 => .core 15 ⟨15,false⟩
    | 1 => .boundary { kind := .unit 0 3, quiver := ⟨2,-3,1,2,-2,6⟩, returnVertex := 1 }
    | 2 => .core 2 ⟨0,false⟩
    | _ => .core 5 ⟨14,false⟩

def delayedRow8 : CoreRow 57 4 where
  quiver := ⟨0,-1,-1,2,-6,2⟩
  word := [2,0]
  edges k := match k.val with
    | 0 => .core 3 ⟨0,false⟩
    | 1 => .core 16 ⟨0,false⟩
    | 2 => .core 5 ⟨14,false⟩
    | _ => .core 17 ⟨0,false⟩

def delayedRow9 : CoreRow 57 4 where
  quiver := ⟨0,1,1,-2,6,-10⟩
  word := [2,1]
  edges k := match k.val with
    | 0 => .core 16 ⟨0,false⟩
    | 1 => .core 3 ⟨0,false⟩
    | 2 => .core 18 ⟨0,false⟩
    | _ => .core 19 ⟨0,false⟩

def delayedRow10 : CoreRow 57 4 where
  quiver := ⟨6,1,-1,-10,6,-2⟩
  word := [2,3]
  edges k := match k.val with
    | 0 => .core 20 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 0 2, quiver := ⟨-6,1,35,10,-6,58⟩, returnVertex := 1 }
    | 2 => .core 21 ⟨0,false⟩
    | _ => .core 3 ⟨0,false⟩

def delayedRow11 : CoreRow 57 4 where
  quiver := ⟨0,-1,-2,-2,4,-1⟩
  word := [0,1,2]
  edges k := match k.val with
    | 0 => .core 15 ⟨1,false⟩
    | 1 => .core 22 ⟨0,false⟩
    | 2 => .core 4 ⟨0,false⟩
    | _ => .core 23 ⟨0,false⟩

def delayedRow12 : CoreRow 57 4 where
  quiver := ⟨-6,-2,3,2,-2,-1⟩
  word := [0,1,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨6,2,-3,2,16,5⟩, returnVertex := 0 }
    | 1 => .boundary { kind := .fork, quiver := ⟨6,-2,-9,-2,2,-5⟩, returnVertex := 1 }
    | 2 => .core 24 ⟨0,false⟩
    | _ => .core 4 ⟨0,false⟩

def delayedRow13 : CoreRow 57 4 where
  quiver := ⟨0,2,-3,-4,2,5⟩
  word := [0,3,0]
  edges k := match k.val with
    | 0 => .core 6 ⟨0,false⟩
    | 1 => .core 25 ⟨0,false⟩
    | 2 => .boundary { kind := .fork, quiver := ⟨8,-2,7,4,2,-5⟩, returnVertex := 2 }
    | _ => .boundary { kind := .fork, quiver := ⟨-6,-13,3,-4,-2,-5⟩, returnVertex := 3 }

def delayedRow14 : CoreRow 57 4 where
  quiver := ⟨0,-2,3,4,-2,7⟩
  word := [0,3,1]
  edges k := match k.val with
    | 0 => .core 25 ⟨0,false⟩
    | 1 => .core 6 ⟨0,false⟩
    | 2 => .boundary { kind := .fork, quiver := ⟨-8,2,3,-4,26,-7⟩, returnVertex := 2 }
    | _ => .boundary { kind := .fork, quiver := ⟨6,-2,-3,-10,2,-7⟩, returnVertex := 3 }

def delayedRow15 : CoreRow 57 4 where
  quiver := ⟨0,2,1,4,-2,1⟩
  word := [0,3,2]
  edges k := match k.val with
    | 0 => .core 11 ⟨1,false⟩
    | 1 => .core 26 ⟨0,false⟩
    | 2 => .core 6 ⟨0,false⟩
    | _ => .core 7 ⟨20,false⟩

def delayedRow16 : CoreRow 57 4 where
  quiver := ⟨0,-1,-1,-2,6,-10⟩
  word := [2,0,1]
  edges k := match k.val with
    | 0 => .core 9 ⟨0,false⟩
    | 1 => .core 8 ⟨0,false⟩
    | 2 => .core 27 ⟨0,false⟩
    | _ => .core 28 ⟨0,false⟩

def delayedRow17 : CoreRow 57 4 where
  quiver := ⟨0,-3,1,-10,6,-2⟩
  word := [2,0,3]
  edges k := match k.val with
    | 0 => .core 20 ⟨21,false⟩
    | 1 => .zero (6) (3) (10) (58) { phase := 0, returnVertex := 1, frame := ⟨0,false⟩, alternateTarget := 20, alternateFrame := ⟨21,false⟩ }
    | 2 => .boundary { kind := .diamond 0 1, quiver := ⟨0,3,-5,10,-14,2⟩, returnVertex := 2 }
    | _ => .core 8 ⟨0,false⟩

def delayedRow18 : CoreRow 57 4 where
  quiver := ⟨2,-1,1,2,-14,10⟩
  word := [2,1,2]
  edges k := match k.val with
    | 0 => .core 29 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 0 3, quiver := ⟨-2,3,1,-2,14,-18⟩, returnVertex := 1 }
    | 2 => .core 9 ⟨0,false⟩
    | _ => .core 30 ⟨0,false⟩

def delayedRow19 : CoreRow 57 4 where
  quiver := ⟨0,11,-1,58,-6,10⟩
  word := [2,1,3]
  edges k := match k.val with
    | 0 => .core 31 ⟨0,false⟩
    | 1 => .zero (6) (11) (58) (338) { phase := 0, returnVertex := 1, frame := ⟨0,true⟩, alternateTarget := 31, alternateFrame := ⟨0,false⟩ }
    | 2 => .boundary { kind := .diamond 0 1, quiver := ⟨0,-11,109,-58,574,-10⟩, returnVertex := 2 }
    | _ => .core 9 ⟨0,false⟩

def delayedRow20 : CoreRow 57 4 where
  quiver := ⟨-6,-1,1,-10,0,-3⟩
  word := [2,3,0]
  edges k := match k.val with
    | 0 => .core 10 ⟨0,false⟩
    | 1 => .zero (6) (3) (10) (58) { phase := 1, returnVertex := 1, frame := ⟨21,false⟩, alternateTarget := 17, alternateFrame := ⟨21,false⟩ }
    | 2 => .core 32 ⟨0,false⟩
    | _ => .core 17 ⟨21,false⟩

def delayedRow21 : CoreRow 57 4 where
  quiver := ⟨16,-1,-1,10,-14,2⟩
  word := [2,3,2]
  edges k := match k.val with
    | 0 => .core 33 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 0 3, quiver := ⟨-16,159,-1,-10,14,-138⟩, returnVertex := 1 }
    | 2 => .core 10 ⟨0,false⟩
    | _ => .core 34 ⟨0,false⟩

def delayedRow22 : CoreRow 57 4 where
  quiver := ⟨0,-1,-2,2,-4,7⟩
  word := [0,1,2,1]
  edges k := match k.val with
    | 0 => .core 26 ⟨1,false⟩
    | 1 => .core 11 ⟨0,false⟩
    | 2 => .core 35 ⟨0,false⟩
    | _ => .boundary { kind := .diamond 0 1, quiver := ⟨0,-15,2,-26,4,-7⟩, returnVertex := 3 }

def delayedRow23 : CoreRow 57 4 where
  quiver := ⟨-8,-1,2,2,-4,1⟩
  word := [0,1,2,3]
  edges k := match k.val with
    | 0 => .core 36 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 0 2, quiver := ⟨8,-1,-30,-2,4,-7⟩, returnVertex := 1 }
    | 2 => .core 24 ⟨1,false⟩
    | _ => .core 11 ⟨0,false⟩

def delayedRow24 : CoreRow 57 4 where
  quiver := ⟨-10,2,1,-2,-2,1⟩
  word := [0,1,3,2]
  edges k := match k.val with
    | 0 => .core 37 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 2 3, quiver := ⟨10,-18,-19,2,2,1⟩, returnVertex := 1 }
    | 2 => .core 12 ⟨0,false⟩
    | _ => .core 23 ⟨1,false⟩

def delayedRow25 : CoreRow 57 4 where
  quiver := ⟨0,2,-3,4,-2,13⟩
  word := [0,3,0,1]
  edges k := match k.val with
    | 0 => .core 14 ⟨0,false⟩
    | 1 => .core 13 ⟨0,false⟩
    | 2 => .boundary { kind := .diamond 0 1, quiver := ⟨0,-2,23,-4,50,-13⟩, returnVertex := 2 }
    | _ => .boundary { kind := .diamond 0 1, quiver := ⟨0,-37,3,-22,2,-13⟩, returnVertex := 3 }

def delayedRow26 : CoreRow 57 4 where
  quiver := ⟨0,2,1,-4,2,-7⟩
  word := [0,3,2,1]
  edges k := match k.val with
    | 0 => .core 22 ⟨1,false⟩
    | 1 => .core 15 ⟨0,false⟩
    | 2 => .boundary { kind := .unit 0 3, quiver := ⟨8,-2,1,4,-26,7⟩, returnVertex := 2 }
    | _ => .core 38 ⟨0,false⟩

def delayedRow27 : CoreRow 57 4 where
  quiver := ⟨0,1,-11,2,-14,10⟩
  word := [2,0,1,2]
  edges k := match k.val with
    | 0 => .core 29 ⟨14,false⟩
    | 1 => .zero (2) (11) (14) (18) { phase := 0, returnVertex := 1, frame := ⟨1,false⟩, alternateTarget := 29, alternateFrame := ⟨14,false⟩ }
    | 2 => .core 16 ⟨0,false⟩
    | _ => .boundary { kind := .diamond 0 1, quiver := ⟨0,-109,11,-138,14,-10⟩, returnVertex := 3 }

def delayedRow28 : CoreRow 57 4 where
  quiver := ⟨-6,-1,1,58,-6,10⟩
  word := [2,0,1,3]
  edges k := match k.val with
    | 0 => .core 31 ⟨21,false⟩
    | 1 => .boundary { kind := .unit 0 2, quiver := ⟨6,-1,-35,-58,6,-338⟩, returnVertex := 1 }
    | 2 => .core 39 ⟨0,false⟩
    | _ => .core 16 ⟨0,false⟩

def delayedRow29 : CoreRow 57 4 where
  quiver := ⟨-2,1,-1,0,-14,11⟩
  word := [2,1,2,0]
  edges k := match k.val with
    | 0 => .core 18 ⟨0,false⟩
    | 1 => .zero (2) (11) (14) (18) { phase := 1, returnVertex := 1, frame := ⟨15,false⟩, alternateTarget := 27, alternateFrame := ⟨14,false⟩ }
    | 2 => .core 27 ⟨14,false⟩
    | _ => .core 40 ⟨0,false⟩

def delayedRow30 : CoreRow 57 4 where
  quiver := ⟨16,-1,-1,-138,14,-10⟩
  word := [2,1,2,3]
  edges k := match k.val with
    | 0 => .core 41 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 0 2, quiver := ⟨-16,-1,223,138,-14,1922⟩, returnVertex := 1 }
    | 2 => .core 42 ⟨0,false⟩
    | _ => .core 18 ⟨0,false⟩

def delayedRow31 : CoreRow 57 4 where
  quiver := ⟨0,-11,1,58,-6,-1⟩
  word := [2,1,3,0]
  edges k := match k.val with
    | 0 => .core 19 ⟨0,false⟩
    | 1 => .zero (6) (11) (58) (338) { phase := 1, returnVertex := 1, frame := ⟨0,true⟩, alternateTarget := 19, alternateFrame := ⟨0,false⟩ }
    | 2 => .core 43 ⟨0,false⟩
    | _ => .core 28 ⟨21,false⟩

def delayedRow32 : CoreRow 57 4 where
  quiver := ⟨-6,1,-2,10,-30,3⟩
  word := [2,3,0,2]
  edges k := match k.val with
    | 0 => .core 33 ⟨14,false⟩
    | 1 => .boundary { kind := .unit 0 2, quiver := ⟨6,1,-182,-10,30,-297⟩, returnVertex := 1 }
    | 2 => .core 20 ⟨0,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨-6,-5,2,-80,30,-3⟩, returnVertex := 3 }

def delayedRow33 : CoreRow 57 4 where
  quiver := ⟨-16,1,1,-6,-30,2⟩
  word := [2,3,2,0]
  edges k := match k.val with
    | 0 => .core 21 ⟨0,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨16,-95,-479,6,30,2⟩, returnVertex := 1 }
    | 2 => .core 32 ⟨14,false⟩
    | _ => .core 44 ⟨0,false⟩

def delayedRow34 : CoreRow 57 4 where
  quiver := ⟨16,-3,1,-18,14,-2⟩
  word := [2,3,2,3]
  edges k := match k.val with
    | 0 => .core 45 ⟨0,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨-16,-3,225,18,-14,250⟩, returnVertex := 1 }
    | 2 => .boundary { kind := .fork, quiver := ⟨16,3,-5,18,-22,2⟩, returnVertex := 2 }
    | _ => .core 21 ⟨0,false⟩

def delayedRow35 : CoreRow 57 4 where
  quiver := ⟨-2,1,-2,-2,10,-7⟩
  word := [0,1,2,1,2]
  edges k := match k.val with
    | 0 => .core 46 ⟨0,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨2,-3,-2,2,-10,13⟩, returnVertex := 1 }
    | 2 => .core 22 ⟨0,false⟩
    | _ => .boundary { kind := .unit 0 2, quiver := ⟨-22,1,2,68,-10,7⟩, returnVertex := 3 }

def delayedRow36 : CoreRow 57 4 where
  quiver := ⟨8,1,-2,2,12,3⟩
  word := [0,1,2,3,0]
  edges k := match k.val with
    | 0 => .core 23 ⟨0,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨-8,17,94,-2,-12,3⟩, returnVertex := 1 }
    | 2 => .core 47 ⟨0,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨-16,-5,2,2,-12,-3⟩, returnVertex := 3 }

def delayedRow37 : CoreRow 57 4 where
  quiver := ⟨10,-2,-1,18,8,1⟩
  word := [0,1,3,2,0]
  edges k := match k.val with
    | 0 => .core 24 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 2 3, quiver := ⟨-10,178,79,-18,-8,1⟩, returnVertex := 1 }
    | 2 => .mstrip 0 (0) 1 ⟨16,true⟩
    | _ => .core 47 ⟨20,false⟩

def delayedRow38 : CoreRow 57 4 where
  quiver := ⟨0,9,-1,10,-2,7⟩
  word := [0,3,2,1,3]
  edges k := match k.val with
    | 0 => .core 46 ⟨20,false⟩
    | 1 => .zero (2) (9) (10) (13) { phase := 0, returnVertex := 1, frame := ⟨0,true⟩, alternateTarget := 46, alternateFrame := ⟨20,false⟩ }
    | 2 => .boundary { kind := .diamond 0 1, quiver := ⟨0,-9,62,-10,68,-7⟩, returnVertex := 2 }
    | _ => .core 26 ⟨0,false⟩

def delayedRow39 : CoreRow 57 4 where
  quiver := ⟨-64,1,1,-58,574,-10⟩
  word := [2,0,1,3,2]
  edges k := match k.val with
    | 0 => .core 49 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 0 3, quiver := ⟨64,-3711,1,58,-574,33282⟩, returnVertex := 1 }
    | 2 => .core 28 ⟨0,false⟩
    | _ => .core 50 ⟨0,false⟩

def delayedRow40 : CoreRow 57 4 where
  quiver := ⟨-2,-10,1,-154,14,-11⟩
  word := [2,1,2,0,3]
  edges k := match k.val with
    | 0 => .core 41 ⟨21,false⟩
    | 1 => .boundary { kind := .unit 0 3, quiver := ⟨2,-318,1,154,-14,2145⟩, returnVertex := 1 }
    | 2 => .boundary { kind := .fork, quiver := ⟨-2,10,-109,154,-1680,11⟩, returnVertex := 2 }
    | _ => .core 29 ⟨0,false⟩

def delayedRow41 : CoreRow 57 4 where
  quiver := ⟨-16,1,1,-154,-2,-10⟩
  word := [2,1,2,3,0]
  edges k := match k.val with
    | 0 => .core 30 ⟨0,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨16,-2463,-31,154,2,-10⟩, returnVertex := 1 }
    | 2 => .core 51 ⟨0,false⟩
    | _ => .core 40 ⟨21,false⟩

def delayedRow42 : CoreRow 57 4 where
  quiver := ⟨16,1,-11,138,-1366,10⟩
  word := [2,1,2,3,2]
  edges k := match k.val with
    | 0 => .core 52 ⟨0,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨-16,2209,-11,-138,1366,-188498⟩, returnVertex := 1 }
    | 2 => .core 30 ⟨0,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨16,-109,11,-13522,1366,-10⟩, returnVertex := 3 }

def delayedRow43 : CoreRow 57 4 where
  quiver := ⟨-638,11,-10,-58,-6,1⟩
  word := [2,1,3,0,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨638,-11,10,6960,-6,-109⟩, returnVertex := 0 }
    | 1 => .boundary { kind := .unit 2 3, quiver := ⟨638,-36993,-3838,58,6,1⟩, returnVertex := 1 }
    | 2 => .core 31 ⟨0,false⟩
    | _ => .core 49 ⟨15,false⟩

def delayedRow44 : CoreRow 57 4 where
  quiver := ⟨14,1,-1,-66,30,-2⟩
  word := [2,3,2,0,3]
  edges k := match k.val with
    | 0 => .core 45 ⟨21,false⟩
    | 1 => .boundary { kind := .unit 0 2, quiver := ⟨-14,1,419,66,-30,1978⟩, returnVertex := 1 }
    | 2 => .mstrip 1 (0) 1 ⟨13,false⟩
    | _ => .core 33 ⟨0,false⟩

def delayedRow45 : CoreRow 57 4 where
  quiver := ⟨-16,3,-1,-66,14,1⟩
  word := [2,3,2,3,0]
  edges k := match k.val with
    | 0 => .core 34 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 0 3, quiver := ⟨16,-1053,-1,66,-14,925⟩, returnVertex := 1 }
    | 2 => .core 53 ⟨15,false⟩
    | _ => .core 44 ⟨21,false⟩

def delayedRow46 : CoreRow 57 4 where
  quiver := ⟨2,-1,2,0,10,-9⟩
  word := [0,1,2,1,2,0]
  edges k := match k.val with
    | 0 => .core 35 ⟨0,false⟩
    | 1 => .zero (2) (9) (10) (13) { phase := 1, returnVertex := 1, frame := ⟨15,true⟩, alternateTarget := 38, alternateFrame := ⟨15,false⟩ }
    | 2 => .core 38 ⟨15,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨2,17,-2,90,-10,9⟩, returnVertex := 3 }

def delayedRow47 : CoreRow 57 4 where
  quiver := ⟨8,-1,1,-2,18,-3⟩
  word := [0,1,2,3,0,2]
  edges k := match k.val with
    | 0 => .core 37 ⟨15,false⟩
    | 1 => .boundary { kind := .unit 0 2, quiver := ⟨-8,-1,145,2,-18,33⟩, returnVertex := 1 }
    | 2 => .core 36 ⟨0,false⟩
    | _ => .core 48 ⟨14,false⟩

def delayedRow48 : CoreRow 57 4 where
  quiver := ⟨-52,-2,3,-8,-18,-1⟩
  word := [0,1,3,2,0,2,3,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨52,2,-3,-8,138,5⟩, returnVertex := 0 }
    | 1 => .boundary { kind := .unit 2 3, quiver := ⟨52,-418,-933,8,18,-1⟩, returnVertex := 1 }
    | 2 => .mstrip 0 (0) 2 ⟨16,true⟩
    | _ => .core 47 ⟨14,false⟩

def delayedRow49 : CoreRow 57 4 where
  quiver := ⟨64,-1,-1,6,638,-10⟩
  word := [2,0,1,3,2,0]
  edges k := match k.val with
    | 0 => .core 39 ⟨0,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨-64,383,40831,-6,-638,-10⟩, returnVertex := 1 }
    | 2 => .core 43 ⟨20,false⟩
    | _ => .core 54 ⟨0,false⟩

def delayedRow50 : CoreRow 57 4 where
  quiver := ⟨-64,11,-1,5682,-574,10⟩
  word := [2,0,1,3,2,3]
  edges k := match k.val with
    | 0 => .core 55 ⟨0,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨64,11,-36737,-5682,574,-3261458⟩, returnVertex := 1 }
    | 2 => .boundary { kind := .fork, quiver := ⟨-64,-11,109,-5682,56246,-10⟩, returnVertex := 2 }
    | _ => .core 39 ⟨0,false⟩

def delayedRow51 : CoreRow 57 4 where
  quiver := ⟨138,-1,1,154,-1542,10⟩
  word := [2,1,2,3,0,2]
  edges k := match k.val with
    | 0 => .core 52 ⟨14,false⟩
    | 1 => .boundary { kind := .unit 0 3, quiver := ⟨-138,21251,1,-154,1542,-237458⟩, returnVertex := 1 }
    | 2 => .core 41 ⟨0,false⟩
    | _ => .mstrip 2 (0) 1 ⟨19,false⟩

def delayedRow52 : CoreRow 57 4 where
  quiver := ⟨-16,-1,11,138,-1542,-1⟩
  word := [2,1,2,3,2,0]
  edges k := match k.val with
    | 0 => .core 42 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 0 2, quiver := ⟨16,-1,-24661,-138,1542,-212797⟩, returnVertex := 1 }
    | 2 => .core 51 ⟨14,false⟩
    | _ => .core 56 ⟨20,false⟩

def delayedRow53 : CoreRow 57 4 where
  quiver := ⟨-66,-1,3,14,-182,-2⟩
  word := [2,3,2,0,3,2,0,2]
  edges k := match k.val with
    | 0 => .core 45 ⟨20,false⟩
    | 1 => .boundary { kind := .unit 0 2, quiver := ⟨66,-1,-12009,-14,182,-2550⟩, returnVertex := 1 }
    | 2 => .mstrip 1 (0) 2 ⟨13,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨480,5,-3,14,182,2⟩, returnVertex := 3 }

def delayedRow54 : CoreRow 57 4 where
  quiver := ⟨-574,-1,1,6386,-638,10⟩
  word := [2,0,1,3,2,0,3]
  edges k := match k.val with
    | 0 => .core 55 ⟨21,false⟩
    | 1 => .boundary { kind := .unit 0 2, quiver := ⟨574,-1,-366211,-6386,638,-4074258⟩, returnVertex := 1 }
    | 2 => .mstrip 3 (0) 1 ⟨13,true⟩
    | _ => .core 49 ⟨0,false⟩

def delayedRow55 : CoreRow 57 4 where
  quiver := ⟨64,-11,1,6386,-574,-1⟩
  word := [2,0,1,3,2,3,0]
  edges k := match k.val with
    | 0 => .core 50 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 0 3, quiver := ⟨-64,408693,1,-6386,574,-3665565⟩, returnVertex := 1 }
    | 2 => .core 57 ⟨15,false⟩
    | _ => .core 54 ⟨21,false⟩

def delayedRow56 : CoreRow 57 4 where
  quiver := ⟨-1542,11,-1,-16946,138,10⟩
  word := [2,1,2,3,0,2,3,0,3]
  edges k := match k.val with
    | 0 => .core 52 ⟨15,false⟩
    | 1 => .boundary { kind := .unit 0 3, quiver := ⟨1542,-26130721,-1,16946,-138,2338558⟩, returnVertex := 1 }
    | 2 => .boundary { kind := .fork, quiver := ⟨184864,-11,109,16946,138,-10⟩, returnVertex := 2 }
    | _ => .mstrip 2 (0) 2 ⟨19,false⟩

def delayedRow57 : CoreRow 57 4 where
  quiver := ⟨6386,1,-11,-574,70182,10⟩
  word := [2,0,1,3,2,0,3,2,0,2]
  edges k := match k.val with
    | 0 => .core 55 ⟨20,false⟩
    | 1 => .boundary { kind := .unit 0 2, quiver := ⟨-6386,1,448182241,574,-70182,40284478⟩, returnVertex := 1 }
    | 2 => .mstrip 3 (0) 2 ⟨13,true⟩
    | _ => .boundary { kind := .fork, quiver := ⟨-765616,-109,11,-574,-70182,-10⟩, returnVertex := 3 }

def delayedStrip0 : StripRecord 57 where
  m := (2)
  a := (18)
  b := (8)
  c := (10)
  rootCore := 37
  rootQuiver := ⟨10,-2,-1,18,8,1⟩
  rootWord := [0,1,3,2,0]
  rootFrame := ⟨16,true⟩
  backward p := match p.val with
    | 0 => ⟨47,⟨11,true⟩⟩
    | 1 => ⟨24,⟨16,true⟩⟩
    | _ => ⟨48,⟨16,true⟩⟩

def delayedStrip1 : StripRecord 57 where
  m := (2)
  a := (66)
  b := (14)
  c := (30)
  rootCore := 44
  rootQuiver := ⟨14,1,-1,-66,30,-2⟩
  rootWord := [2,3,2,0,3]
  rootFrame := ⟨13,false⟩
  backward p := match p.val with
    | 0 => ⟨45,⟨16,false⟩⟩
    | 1 => ⟨33,⟨10,false⟩⟩
    | _ => ⟨53,⟨10,false⟩⟩

def delayedStrip2 : StripRecord 57 where
  m := (10)
  a := (1542)
  b := (138)
  c := (154)
  rootCore := 51
  rootQuiver := ⟨138,-1,1,154,-1542,10⟩
  rootWord := [2,1,2,3,0,2]
  rootFrame := ⟨19,false⟩
  backward p := match p.val with
    | 0 => ⟨52,⟨17,false⟩⟩
    | 1 => ⟨41,⟨11,false⟩⟩
    | _ => ⟨56,⟨11,false⟩⟩

def delayedStrip3 : StripRecord 57 where
  m := (10)
  a := (6386)
  b := (574)
  c := (638)
  rootCore := 54
  rootQuiver := ⟨-574,-1,1,6386,-638,10⟩
  rootWord := [2,0,1,3,2,0,3]
  rootFrame := ⟨13,true⟩
  backward p := match p.val with
    | 0 => ⟨55,⟨16,true⟩⟩
    | 1 => ⟨49,⟨10,true⟩⟩
    | _ => ⟨57,⟨10,true⟩⟩

def delayed : Certificate where
  initial := ⟨0,-1,3,-2,-2,-2⟩
  entryWord := []
  entryFrame := ⟨0,false⟩
  size := 57
  stripCount := 4
  core i := match i.val with
    | 0 => delayedRow0
    | 1 => delayedRow1
    | 2 => delayedRow2
    | 3 => delayedRow3
    | 4 => delayedRow4
    | 5 => delayedRow5
    | 6 => delayedRow6
    | 7 => delayedRow7
    | 8 => delayedRow8
    | 9 => delayedRow9
    | 10 => delayedRow10
    | 11 => delayedRow11
    | 12 => delayedRow12
    | 13 => delayedRow13
    | 14 => delayedRow14
    | 15 => delayedRow15
    | 16 => delayedRow16
    | 17 => delayedRow17
    | 18 => delayedRow18
    | 19 => delayedRow19
    | 20 => delayedRow20
    | 21 => delayedRow21
    | 22 => delayedRow22
    | 23 => delayedRow23
    | 24 => delayedRow24
    | 25 => delayedRow25
    | 26 => delayedRow26
    | 27 => delayedRow27
    | 28 => delayedRow28
    | 29 => delayedRow29
    | 30 => delayedRow30
    | 31 => delayedRow31
    | 32 => delayedRow32
    | 33 => delayedRow33
    | 34 => delayedRow34
    | 35 => delayedRow35
    | 36 => delayedRow36
    | 37 => delayedRow37
    | 38 => delayedRow38
    | 39 => delayedRow39
    | 40 => delayedRow40
    | 41 => delayedRow41
    | 42 => delayedRow42
    | 43 => delayedRow43
    | 44 => delayedRow44
    | 45 => delayedRow45
    | 46 => delayedRow46
    | 47 => delayedRow47
    | 48 => delayedRow48
    | 49 => delayedRow49
    | 50 => delayedRow50
    | 51 => delayedRow51
    | 52 => delayedRow52
    | 53 => delayedRow53
    | 54 => delayedRow54
    | 55 => delayedRow55
    | 56 => delayedRow56
    | _ => delayedRow57
  strips s := match s.val with
    | 0 => delayedStrip0
    | 1 => delayedStrip1
    | 2 => delayedStrip2
    | _ => delayedStrip3
  triangleAvoidance := true

def smithRow0 : CoreRow 12 1 where
  quiver := ⟨0,0,4,2,-1,1⟩
  word := []
  edges k := match k.val with
    | 0 => .core 0 ⟨2,true⟩
    | 1 => .core 0 ⟨2,false⟩
    | 2 => .core 0 ⟨2,false⟩
    | _ => .core 1 ⟨0,false⟩

def smithRow1 : CoreRow 12 1 where
  quiver := ⟨4,0,-4,1,1,-1⟩
  word := [3]
  edges k := match k.val with
    | 0 => .core 2 ⟨0,false⟩
    | 1 => .core 1 ⟨1,true⟩
    | 2 => .core 1 ⟨5,true⟩
    | _ => .core 0 ⟨0,false⟩

def smithRow2 : CoreRow 12 1 where
  quiver := ⟨-4,0,4,1,-15,-1⟩
  word := [3,0]
  edges k := match k.val with
    | 0 => .core 1 ⟨0,false⟩
    | 1 => .core 3 ⟨0,false⟩
    | 2 => .core 2 ⟨5,true⟩
    | _ => .core 4 ⟨0,false⟩

def smithRow3 : CoreRow 12 1 where
  quiver := ⟨4,0,-56,-1,15,-16⟩
  word := [3,0,1]
  edges k := match k.val with
    | 0 => .zero (4) (16) (56) (209) { phase := 0, returnVertex := 0, frame := ⟨13,false⟩, alternateTarget := 5, alternateFrame := ⟨0,false⟩ }
    | 1 => .core 2 ⟨0,false⟩
    | 2 => .core 5 ⟨0,false⟩
    | _ => .boundary { kind := .diamond 0 2, quiver := ⟨-836,0,56,239,-15,16⟩, returnVertex := 3 }

def smithRow4 : CoreRow 12 1 where
  quiver := ⟨56,4,-4,1,15,1⟩
  word := [3,0,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 2, quiver := ⟨-56,-4,4,1,-209,-15⟩, returnVertex := 0 }
    | 1 => .core 6 ⟨0,false⟩
    | 2 => .core 5 ⟨3,true⟩
    | _ => .core 2 ⟨0,false⟩

def smithRow5 : CoreRow 12 1 where
  quiver := ⟨4,0,-56,1,-1,16⟩
  word := [3,0,1,2]
  edges k := match k.val with
    | 0 => .zero (4) (16) (56) (209) { phase := 1, returnVertex := 0, frame := ⟨13,false⟩, alternateTarget := 3, alternateFrame := ⟨0,false⟩ }
    | 1 => .core 4 ⟨4,true⟩
    | 2 => .core 3 ⟨0,false⟩
    | _ => .core 7 ⟨0,false⟩

def smithRow6 : CoreRow 12 1 where
  quiver := ⟨-56,60,836,-1,-15,1⟩
  word := [3,0,3,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 2 3, quiver := ⟨56,-60,-836,3359,46801,1⟩, returnVertex := 0 }
    | 1 => .core 4 ⟨0,false⟩
    | 2 => .core 8 ⟨0,false⟩
    | _ => .core 9 ⟨0,false⟩

def smithRow7 : CoreRow 12 1 where
  quiver := ⟨4,-896,56,-15,1,-16⟩
  word := [3,0,1,2,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 3, quiver := ⟨-4,896,-56,-3599,1,50160⟩, returnVertex := 0 }
    | 1 => .core 8 ⟨1,true⟩
    | 2 => .boundary { kind := .fork, quiver := ⟨4,896,-14280,15,-239,16⟩, returnVertex := 2 }
    | _ => .core 5 ⟨0,false⟩

def smithRow8 : CoreRow 12 1 where
  quiver := ⟨4,-60,896,1,-15,-1⟩
  word := [3,0,3,1,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨-4,60,-896,-239,-15,53759⟩, returnVertex := 0 }
    | 1 => .core 7 ⟨1,true⟩
    | 2 => .core 6 ⟨0,false⟩
    | _ => .core 10 ⟨0,false⟩

def smithRow9 : CoreRow 12 1 where
  quiver := ⟨12484,60,-836,-16,15,-1⟩
  word := [3,0,3,1,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨-12484,-60,836,-16,-10436609,-50161⟩, returnVertex := 0 }
    | 1 => .boundary { kind := .fork, quiver := ⟨-12484,60,186424,16,-15,239⟩, returnVertex := 1 }
    | 2 => .core 11 ⟨0,false⟩
    | _ => .core 6 ⟨0,false⟩

def smithRow10 : CoreRow 12 1 where
  quiver := ⟨13444,836,-896,1,15,1⟩
  word := [3,0,3,1,2,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 2, quiver := ⟨-13444,-836,896,1,-12045809,-749055⟩, returnVertex := 0 }
    | 1 => .mstrip 0 (0) 1 ⟨9,true⟩
    | 2 => .core 11 ⟨1,false⟩
    | _ => .core 8 ⟨0,false⟩

def smithRow11 : CoreRow 12 1 where
  quiver := ⟨13444,-60,-836,16,-1,1⟩
  word := [3,0,3,1,3,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 2 3, quiver := ⟨-13444,60,836,-806624,-11239185,1⟩, returnVertex := 0 }
    | 1 => .core 12 ⟨4,false⟩
    | 2 => .core 9 ⟨0,false⟩
    | _ => .core 10 ⟨1,false⟩

def smithRow12 : CoreRow 12 1 where
  quiver := ⟨-836,-13444,215044,-1,15,-16⟩
  word := [3,0,3,1,2,3,1,2,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 2, quiver := ⟨836,13444,-215044,-1,179776799,2891051520⟩, returnVertex := 0 }
    | 1 => .mstrip 0 (0) 2 ⟨9,true⟩
    | 2 => .core 11 ⟨3,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨-836,3427260,-215044,239,-15,16⟩, returnVertex := 3 }

def smithStrip0 : StripRecord 12 where
  m := (15)
  a := (13444)
  b := (836)
  c := (896)
  rootCore := 10
  rootQuiver := ⟨13444,836,-896,1,15,1⟩
  rootWord := [3,0,3,1,2,3]
  rootFrame := ⟨9,true⟩
  backward p := match p.val with
    | 0 => ⟨11,⟨19,true⟩⟩
    | 1 => ⟨8,⟨18,true⟩⟩
    | _ => ⟨12,⟨18,true⟩⟩

def smith : Certificate where
  initial := ⟨0,0,4,2,-1,1⟩
  entryWord := []
  entryFrame := ⟨0,false⟩
  size := 12
  stripCount := 1
  core i := match i.val with
    | 0 => smithRow0
    | 1 => smithRow1
    | 2 => smithRow2
    | 3 => smithRow3
    | 4 => smithRow4
    | 5 => smithRow5
    | 6 => smithRow6
    | 7 => smithRow7
    | 8 => smithRow8
    | 9 => smithRow9
    | 10 => smithRow10
    | 11 => smithRow11
    | _ => smithRow12
  strips s := match s.val with
    | _ => smithStrip0
  triangleAvoidance := true

def cosquareRow0 : CoreRow 19 0 where
  quiver := ⟨-2,2,-1,4,0,5⟩
  word := []
  edges k := match k.val with
    | 0 => .core 1 ⟨0,false⟩
    | 1 => .core 2 ⟨0,false⟩
    | 2 => .boundary { kind := .fork, quiver := ⟨-2,-2,9,-4,20,-5⟩, returnVertex := 2 }
    | _ => .core 3 ⟨0,false⟩

def cosquareRow1 : CoreRow 19 0 where
  quiver := ⟨2,-2,1,8,0,3⟩
  word := [0]
  edges k := match k.val with
    | 0 => .core 0 ⟨0,false⟩
    | 1 => .core 4 ⟨0,false⟩
    | 2 => .boundary { kind := .unit 0 3, quiver := ⟨-14,2,1,-8,24,-3⟩, returnVertex := 2 }
    | _ => .core 5 ⟨0,false⟩

def cosquareRow2 : CoreRow 19 0 where
  quiver := ⟨2,2,-1,-4,0,5⟩
  word := [1]
  edges k := match k.val with
    | 0 => .core 6 ⟨0,false⟩
    | 1 => .core 0 ⟨0,false⟩
    | 2 => .boundary { kind := .diamond 1 3, quiver := ⟨10,-2,9,4,0,-5⟩, returnVertex := 2 }
    | _ => .core 7 ⟨0,false⟩

def cosquareRow3 : CoreRow 19 0 where
  quiver := ⟨-2,-3,1,4,0,-5⟩
  word := [3]
  edges k := match k.val with
    | 0 => .core 8 ⟨0,false⟩
    | 1 => .core 7 ⟨0,false⟩
    | 2 => .boundary { kind := .diamond 1 3, quiver := ⟨-14,3,-14,-4,0,5⟩, returnVertex := 2 }
    | _ => .core 0 ⟨0,false⟩

def cosquareRow4 : CoreRow 19 0 where
  quiver := ⟨-2,14,1,-8,0,3⟩
  word := [0,1]
  edges k := match k.val with
    | 0 => .core 9 ⟨0,false⟩
    | 1 => .core 1 ⟨0,false⟩
    | 2 => .boundary { kind := .diamond 1 3, quiver := ⟨110,-14,43,8,0,-3⟩, returnVertex := 2 }
    | _ => .core 10 ⟨0,false⟩

def cosquareRow5 : CoreRow 19 0 where
  quiver := ⟨2,-2,-1,8,0,-3⟩
  word := [0,3]
  edges k := match k.val with
    | 0 => .core 8 ⟨21,false⟩
    | 1 => .core 10 ⟨0,false⟩
    | 2 => .boundary { kind := .diamond 1 3, quiver := ⟨-14,2,-7,-8,0,3⟩, returnVertex := 2 }
    | _ => .core 1 ⟨0,false⟩

def cosquareRow6 : CoreRow 19 0 where
  quiver := ⟨-2,-2,1,-4,-2,3⟩
  word := [1,0]
  edges k := match k.val with
    | 0 => .core 2 ⟨0,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨2,-10,-3,4,2,3⟩, returnVertex := 1 }
    | 2 => .core 8 ⟨21,false⟩
    | _ => .core 11 ⟨0,false⟩

def cosquareRow7 : CoreRow 19 0 where
  quiver := ⟨2,-3,1,-4,0,-5⟩
  word := [1,3]
  edges k := match k.val with
    | 0 => .core 12 ⟨0,false⟩
    | 1 => .core 3 ⟨0,false⟩
    | 2 => .boundary { kind := .fork, quiver := ⟨2,3,-14,4,-20,5⟩, returnVertex := 2 }
    | _ => .core 2 ⟨0,false⟩

def cosquareRow8 : CoreRow 19 0 where
  quiver := ⟨2,3,-1,4,2,-2⟩
  word := [3,0]
  edges k := match k.val with
    | 0 => .core 3 ⟨0,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨-2,11,3,-4,-2,-2⟩, returnVertex := 1 }
    | 2 => .core 6 ⟨21,false⟩
    | _ => .core 5 ⟨21,false⟩

def cosquareRow9 : CoreRow 19 0 where
  quiver := ⟨2,-14,-1,20,2,3⟩
  word := [0,1,0]
  edges k := match k.val with
    | 0 => .core 4 ⟨0,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨-2,26,3,-20,-2,3⟩, returnVertex := 1 }
    | 2 => .boundary { kind := .unit 0 3, quiver := ⟨-278,14,-1,-20,62,-3⟩, returnVertex := 2 }
    | _ => .core 13 ⟨0,false⟩

def cosquareRow10 : CoreRow 19 0 where
  quiver := ⟨-2,14,-1,-8,0,-3⟩
  word := [0,1,3]
  edges k := match k.val with
    | 0 => .core 14 ⟨0,false⟩
    | 1 => .core 5 ⟨0,false⟩
    | 2 => .boundary { kind := .unit 0 3, quiver := ⟨110,-14,-1,8,-24,3⟩, returnVertex := 2 }
    | _ => .core 4 ⟨0,false⟩

def cosquareRow11 : CoreRow 19 0 where
  quiver := ⟨0,-2,-1,-10,2,-3⟩
  word := [1,0,3]
  edges k := match k.val with
    | 0 => .core 12 ⟨21,false⟩
    | 1 => .core 15 ⟨0,false⟩
    | 2 => .boundary { kind := .diamond 0 1, quiver := ⟨0,2,-7,10,-28,3⟩, returnVertex := 2 }
    | _ => .core 6 ⟨0,false⟩

def cosquareRow12 : CoreRow 19 0 where
  quiver := ⟨-2,3,-1,-10,0,-2⟩
  word := [1,3,0]
  edges k := match k.val with
    | 0 => .core 7 ⟨0,false⟩
    | 1 => .core 16 ⟨0,false⟩
    | 2 => .boundary { kind := .unit 0 3, quiver := ⟨28,-3,-1,10,-20,2⟩, returnVertex := 2 }
    | _ => .core 11 ⟨21,false⟩

def cosquareRow13 : CoreRow 19 0 where
  quiver := ⟨0,-17,1,20,-2,-3⟩
  word := [0,1,0,3]
  edges k := match k.val with
    | 0 => .core 14 ⟨21,false⟩
    | 1 => .zero (2) (17) (20) (26) { phase := 1, returnVertex := 1, frame := ⟨0,true⟩, alternateTarget := 14, alternateFrame := ⟨21,false⟩ }
    | 2 => .boundary { kind := .fork, quiver := ⟨-340,17,-50,-20,-2,3⟩, returnVertex := 2 }
    | _ => .core 9 ⟨0,false⟩

def cosquareRow14 : CoreRow 19 0 where
  quiver := ⟨2,-14,1,20,0,-17⟩
  word := [0,1,3,0]
  edges k := match k.val with
    | 0 => .core 10 ⟨0,false⟩
    | 1 => .zero (2) (17) (20) (26) { phase := 0, returnVertex := 1, frame := ⟨21,true⟩, alternateTarget := 13, alternateFrame := ⟨21,false⟩ }
    | 2 => .boundary { kind := .diamond 1 3, quiver := ⟨-278,14,-237,-20,0,17⟩, returnVertex := 2 }
    | _ => .core 13 ⟨21,false⟩

def cosquareRow15 : CoreRow 19 0 where
  quiver := ⟨0,-2,-1,10,-2,17⟩
  word := [1,0,3,1]
  edges k := match k.val with
    | 0 => .core 16 ⟨21,false⟩
    | 1 => .core 11 ⟨0,false⟩
    | 2 => .boundary { kind := .unit 0 3, quiver := ⟨-20,2,-1,-10,168,-17⟩, returnVertex := 2 }
    | _ => .core 17 ⟨0,false⟩

def cosquareRow16 : CoreRow 19 0 where
  quiver := ⟨2,-17,-1,10,0,-2⟩
  word := [1,3,0,1]
  edges k := match k.val with
    | 0 => .core 18 ⟨0,false⟩
    | 1 => .core 12 ⟨0,false⟩
    | 2 => .boundary { kind := .diamond 1 3, quiver := ⟨-168,17,-35,-10,0,2⟩, returnVertex := 2 }
    | _ => .core 15 ⟨21,false⟩

def cosquareRow17 : CoreRow 19 0 where
  quiver := ⟨0,-19,1,-24,2,-17⟩
  word := [1,0,3,1,3]
  edges k := match k.val with
    | 0 => .core 19 ⟨0,false⟩
    | 1 => .zero (2) (19) (24) (31) { phase := 0, returnVertex := 1, frame := ⟨0,false⟩, alternateTarget := 19, alternateFrame := ⟨0,false⟩ }
    | 2 => .boundary { kind := .diamond 0 1, quiver := ⟨0,19,-322,24,-406,17⟩, returnVertex := 2 }
    | _ => .core 15 ⟨0,false⟩

def cosquareRow18 : CoreRow 19 0 where
  quiver := ⟨-2,17,1,-24,-2,-2⟩
  word := [1,3,0,1,0]
  edges k := match k.val with
    | 0 => .core 16 ⟨0,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨2,-31,-3,24,2,-2⟩, returnVertex := 1 }
    | 2 => .boundary { kind := .unit 0 3, quiver := ⟨406,-17,1,24,-50,2⟩, returnVertex := 2 }
    | _ => .core 19 ⟨0,false⟩

def cosquareRow19 : CoreRow 19 0 where
  quiver := ⟨0,19,-1,-24,2,2⟩
  word := [1,0,3,1,3,0]
  edges k := match k.val with
    | 0 => .core 17 ⟨0,false⟩
    | 1 => .zero (2) (19) (24) (31) { phase := 1, returnVertex := 1, frame := ⟨0,false⟩, alternateTarget := 17, alternateFrame := ⟨0,false⟩ }
    | 2 => .boundary { kind := .fork, quiver := ⟨456,-19,37,24,2,-2⟩, returnVertex := 2 }
    | _ => .core 18 ⟨0,false⟩

def cosquare : Certificate where
  initial := ⟨-2,2,-1,4,0,5⟩
  entryWord := []
  entryFrame := ⟨0,false⟩
  size := 19
  stripCount := 0
  core i := match i.val with
    | 0 => cosquareRow0
    | 1 => cosquareRow1
    | 2 => cosquareRow2
    | 3 => cosquareRow3
    | 4 => cosquareRow4
    | 5 => cosquareRow5
    | 6 => cosquareRow6
    | 7 => cosquareRow7
    | 8 => cosquareRow8
    | 9 => cosquareRow9
    | 10 => cosquareRow10
    | 11 => cosquareRow11
    | 12 => cosquareRow12
    | 13 => cosquareRow13
    | 14 => cosquareRow14
    | 15 => cosquareRow15
    | 16 => cosquareRow16
    | 17 => cosquareRow17
    | 18 => cosquareRow18
    | _ => cosquareRow19
  strips := Fin.elim0
  triangleAvoidance := true

def antiRow0 : CoreRow 88 8 where
  quiver := ⟨1,6,0,1,-4,1⟩
  word := []
  edges k := match k.val with
    | 0 => .core 1 ⟨0,false⟩
    | 1 => .core 2 ⟨0,false⟩
    | 2 => .core 3 ⟨0,false⟩
    | _ => .core 4 ⟨0,false⟩

def antiRow1 : CoreRow 88 8 where
  quiver := ⟨-1,-6,0,1,-4,1⟩
  word := [0]
  edges k := match k.val with
    | 0 => .core 0 ⟨0,false⟩
    | 1 => .core 5 ⟨0,false⟩
    | 2 => .core 6 ⟨0,false⟩
    | _ => .core 7 ⟨0,false⟩

def antiRow2 : CoreRow 88 8 where
  quiver := ⟨-1,7,0,-1,4,-3⟩
  word := [1]
  edges k := match k.val with
    | 0 => .core 8 ⟨0,false⟩
    | 1 => .core 0 ⟨0,false⟩
    | 2 => .core 9 ⟨0,false⟩
    | _ => .core 10 ⟨0,false⟩

def antiRow3 : CoreRow 88 8 where
  quiver := ⟨1,-6,6,-1,-3,-1⟩
  word := [2]
  edges k := match k.val with
    | 0 => .core 11 ⟨0,false⟩
    | 1 => .core 12 ⟨0,false⟩
    | 2 => .core 0 ⟨0,false⟩
    | _ => .core 13 ⟨0,false⟩

def antiRow4 : CoreRow 88 8 where
  quiver := ⟨1,6,0,-3,4,-1⟩
  word := [3]
  edges k := match k.val with
    | 0 => .core 7 ⟨0,false⟩
    | 1 => .core 14 ⟨0,false⟩
    | 2 => .core 15 ⟨0,false⟩
    | _ => .core 0 ⟨0,false⟩

def antiRow5 : CoreRow 88 8 where
  quiver := ⟨1,-6,-4,-1,4,-3⟩
  word := [0,1]
  edges k := match k.val with
    | 0 => .core 8 ⟨6,false⟩
    | 1 => .core 1 ⟨0,false⟩
    | 2 => .core 16 ⟨0,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨-15,-6,4,11,-4,3⟩, returnVertex := 3 }

def antiRow6 : CoreRow 88 8 where
  quiver := ⟨-7,6,0,-1,-3,-1⟩
  word := [0,2]
  edges k := match k.val with
    | 0 => .core 17 ⟨0,false⟩
    | 1 => .core 18 ⟨0,false⟩
    | 2 => .core 1 ⟨0,false⟩
    | _ => .core 9 ⟨2,false⟩

def antiRow7 : CoreRow 88 8 where
  quiver := ⟨-1,-6,0,-3,4,-1⟩
  word := [0,3]
  edges k := match k.val with
    | 0 => .core 4 ⟨0,false⟩
    | 1 => .core 19 ⟨0,false⟩
    | 2 => .core 12 ⟨1,false⟩
    | _ => .core 1 ⟨0,false⟩

def antiRow8 : CoreRow 88 8 where
  quiver := ⟨1,-7,0,6,4,-3⟩
  word := [1,0]
  edges k := match k.val with
    | 0 => .core 2 ⟨0,false⟩
    | 1 => .core 5 ⟨6,false⟩
    | 2 => .boundary { kind := .fork, quiver := ⟨-41,7,-21,-6,4,3⟩, returnVertex := 2 }
    | _ => .core 20 ⟨0,false⟩

def antiRow9 : CoreRow 88 8 where
  quiver := ⟨6,-7,0,1,1,3⟩
  word := [1,2]
  edges k := match k.val with
    | 0 => .core 21 ⟨0,false⟩
    | 1 => .core 12 ⟨2,false⟩
    | 2 => .core 2 ⟨0,false⟩
    | _ => .core 6 ⟨2,false⟩

def antiRow10 : CoreRow 88 8 where
  quiver := ⟨-1,7,0,11,-4,3⟩
  word := [1,3]
  edges k := match k.val with
    | 0 => .core 20 ⟨0,false⟩
    | 1 => .core 22 ⟨0,false⟩
    | 2 => .boundary { kind := .unit 0 1, quiver := ⟨-1,-7,21,-11,29,-3⟩, returnVertex := 2 }
    | _ => .core 2 ⟨0,false⟩

def antiRow11 : CoreRow 88 8 where
  quiver := ⟨-1,6,-6,-7,-3,35⟩
  word := [2,0]
  edges k := match k.val with
    | 0 => .core 3 ⟨0,false⟩
    | 1 => .core 23 ⟨0,false⟩
    | 2 => .boundary { kind := .fork, quiver := ⟨41,-6,204,7,-3,-35⟩, returnVertex := 2 }
    | _ => .boundary { kind := .unit 0 1, quiver := ⟨-1,-204,6,-112,3,-35⟩, returnVertex := 3 }

def antiRow12 : CoreRow 88 8 where
  quiver := ⟨-1,-6,6,1,3,-1⟩
  word := [2,1]
  edges k := match k.val with
    | 0 => .core 24 ⟨0,false⟩
    | 1 => .core 3 ⟨0,false⟩
    | 2 => .core 9 ⟨2,false⟩
    | _ => .core 7 ⟨1,false⟩

def antiRow13 : CoreRow 88 8 where
  quiver := ⟨19,0,-6,-1,3,1⟩
  word := [2,3]
  edges k := match k.val with
    | 0 => .core 25 ⟨0,false⟩
    | 1 => .core 26 ⟨0,false⟩
    | 2 => .core 15 ⟨1,false⟩
    | _ => .core 3 ⟨0,false⟩

def antiRow14 : CoreRow 88 8 where
  quiver := ⟨-1,6,4,3,-4,11⟩
  word := [3,1]
  edges k := match k.val with
    | 0 => .core 27 ⟨0,false⟩
    | 1 => .core 4 ⟨0,false⟩
    | 2 => .boundary { kind := .unit 0 1, quiver := ⟨-1,-6,70,-3,29,-11⟩, returnVertex := 2 }
    | _ => .boundary { kind := .fork, quiver := ⟨15,6,-4,-41,4,-11⟩, returnVertex := 3 }

def antiRow15 : CoreRow 88 8 where
  quiver := ⟨19,-6,0,3,1,1⟩
  word := [3,2]
  edges k := match k.val with
    | 0 => .core 28 ⟨0,false⟩
    | 1 => .core 29 ⟨0,false⟩
    | 2 => .core 4 ⟨0,false⟩
    | _ => .core 13 ⟨1,false⟩

def antiRow16 : CoreRow 88 8 where
  quiver := ⟨1,6,-22,1,1,3⟩
  word := [0,1,2]
  edges k := match k.val with
    | 0 => .core 30 ⟨0,false⟩
    | 1 => .core 18 ⟨2,false⟩
    | 2 => .core 5 ⟨0,false⟩
    | _ => .core 31 ⟨0,false⟩

def antiRow17 : CoreRow 88 8 where
  quiver := ⟨7,-6,0,41,-3,-1⟩
  word := [0,2,0]
  edges k := match k.val with
    | 0 => .core 6 ⟨0,false⟩
    | 1 => .boundary { kind := .diamond 0 3, quiver := ⟨-7,281,0,-41,3,-124⟩, returnVertex := 1 }
    | 2 => .core 32 ⟨0,false⟩
    | _ => .core 21 ⟨2,false⟩

def antiRow18 : CoreRow 88 8 where
  quiver := ⟨7,-1,-21,1,3,-1⟩
  word := [0,2,1]
  edges k := match k.val with
    | 0 => .core 33 ⟨0,false⟩
    | 1 => .core 6 ⟨0,false⟩
    | 2 => .core 16 ⟨2,false⟩
    | _ => .core 34 ⟨0,false⟩

def antiRow19 : CoreRow 88 8 where
  quiver := ⟨1,-9,0,3,-4,11⟩
  word := [0,3,1]
  edges k := match k.val with
    | 0 => .core 27 ⟨6,false⟩
    | 1 => .core 7 ⟨0,false⟩
    | 2 => .boundary { kind := .diamond 0 3, quiver := ⟨-26,9,0,-3,29,-11⟩, returnVertex := 2 }
    | _ => .zero (4) (9) (11) (41) { phase := 0, returnVertex := 3, frame := ⟨5,false⟩, alternateTarget := 27, alternateFrame := ⟨6,false⟩ }

def antiRow20 : CoreRow 88 8 where
  quiver := ⟨1,-7,0,18,-4,3⟩
  word := [1,0,3]
  edges k := match k.val with
    | 0 => .core 10 ⟨0,false⟩
    | 1 => .core 35 ⟨0,false⟩
    | 2 => .boundary { kind := .diamond 0 3, quiver := ⟨-125,7,0,-18,50,-3⟩, returnVertex := 2 }
    | _ => .core 8 ⟨0,false⟩

def antiRow21 : CoreRow 88 8 where
  quiver := ⟨-6,7,0,-41,1,3⟩
  word := [1,2,0]
  edges k := match k.val with
    | 0 => .core 9 ⟨0,false⟩
    | 1 => .core 36 ⟨0,false⟩
    | 2 => .boundary { kind := .unit 1 3, quiver := ⟨281,-7,21,41,1,-3⟩, returnVertex := 2 }
    | _ => .core 17 ⟨2,false⟩

def antiRow22 : CoreRow 88 8 where
  quiver := ⟨1,7,-4,-11,4,-41⟩
  word := [1,3,1]
  edges k := match k.val with
    | 0 => .core 37 ⟨0,false⟩
    | 1 => .core 10 ⟨0,false⟩
    | 2 => .boundary { kind := .fork, quiver := ⟨78,-7,-4,11,-447,41⟩, returnVertex := 2 }
    | _ => .boundary { kind := .fork, quiver := ⟨-15,7,4,153,-4,41⟩, returnVertex := 3 }

def antiRow23 : CoreRow 88 8 where
  quiver := ⟨1,-1,-9,7,3,35⟩
  word := [2,0,1]
  edges k := match k.val with
    | 0 => .core 24 ⟨6,false⟩
    | 1 => .core 11 ⟨0,false⟩
    | 2 => .core 38 ⟨0,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨-26,-316,9,7,-3,-35⟩, returnVertex := 3 }

def antiRow24 : CoreRow 88 8 where
  quiver := ⟨1,6,-6,1,9,35⟩
  word := [2,1,0]
  edges k := match k.val with
    | 0 => .core 12 ⟨0,false⟩
    | 1 => .core 23 ⟨6,false⟩
    | 2 => .core 39 ⟨0,false⟩
    | _ => .boundary { kind := .unit 1 2, quiver := ⟨-53,-204,6,1,-9,-35⟩, returnVertex := 3 }

def antiRow25 : CoreRow 88 8 where
  quiver := ⟨-19,0,6,-1,-111,1⟩
  word := [2,3,0]
  edges k := match k.val with
    | 0 => .core 13 ⟨0,false⟩
    | 1 => .core 40 ⟨0,false⟩
    | 2 => .core 28 ⟨1,false⟩
    | _ => .core 41 ⟨0,false⟩

def antiRow26 : CoreRow 88 8 where
  quiver := ⟨-19,0,51,1,-3,4⟩
  word := [2,3,1]
  edges k := match k.val with
    | 0 => .zero (19) (4) (51) (966) { phase := 0, returnVertex := 0, frame := ⟨13,true⟩, alternateTarget := 42, alternateFrame := ⟨0,false⟩ }
    | 1 => .core 13 ⟨0,false⟩
    | 2 => .core 42 ⟨0,false⟩
    | _ => .boundary { kind := .diamond 0 2, quiver := ⟨134,0,-51,-11,3,-4⟩, returnVertex := 3 }

def antiRow27 : CoreRow 88 8 where
  quiver := ⟨1,-6,-4,9,0,11⟩
  word := [3,1,0]
  edges k := match k.val with
    | 0 => .core 14 ⟨0,false⟩
    | 1 => .core 19 ⟨6,false⟩
    | 2 => .boundary { kind := .fork, quiver := ⟨-53,6,-4,-9,99,-11⟩, returnVertex := 2 }
    | _ => .zero (4) (9) (11) (41) { phase := 1, returnVertex := 3, frame := ⟨11,false⟩, alternateTarget := 19, alternateFrame := ⟨6,false⟩ }

def antiRow28 : CoreRow 88 8 where
  quiver := ⟨-19,6,0,-111,1,1⟩
  word := [3,2,0]
  edges k := match k.val with
    | 0 => .core 15 ⟨0,false⟩
    | 1 => .core 43 ⟨0,false⟩
    | 2 => .core 44 ⟨0,false⟩
    | _ => .core 25 ⟨1,false⟩

def antiRow29 : CoreRow 88 8 where
  quiver := ⟨-19,51,19,-3,-1,1⟩
  word := [3,2,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 2 3, quiver := ⟨19,-51,-19,966,360,1⟩, returnVertex := 0 }
    | 1 => .core 15 ⟨0,false⟩
    | 2 => .core 45 ⟨0,false⟩
    | _ => .core 42 ⟨4,false⟩

def antiRow30 : CoreRow 88 8 where
  quiver := ⟨-1,-6,22,1,-21,-129⟩
  word := [0,1,2,0]
  edges k := match k.val with
    | 0 => .core 16 ⟨0,false⟩
    | 1 => .core 46 ⟨0,false⟩
    | 2 => .core 47 ⟨0,false⟩
    | _ => .boundary { kind := .unit 1 2, quiver := ⟨461,2832,-22,1,21,129⟩, returnVertex := 3 }

def antiRow31 : CoreRow 88 8 where
  quiver := ⟨-21,-60,22,1,-1,-3⟩
  word := [0,1,2,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 2, quiver := ⟨21,60,-22,1,461,1317⟩, returnVertex := 0 }
    | 1 => .core 48 ⟨0,false⟩
    | 2 => .mstrip 0 (0) 1 ⟨15,false⟩
    | _ => .core 16 ⟨0,false⟩

def antiRow32 : CoreRow 88 8 where
  quiver := ⟨-239,6,-6,-41,-3,1⟩
  word := [0,2,0,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨239,-6,6,1393,-3,-35⟩, returnVertex := 0 }
    | 1 => .boundary { kind := .unit 2 3, quiver := ⟨239,-9793,-723,41,3,1⟩, returnVertex := 1 }
    | 2 => .core 17 ⟨0,false⟩
    | _ => .core 50 ⟨0,false⟩

def antiRow33 : CoreRow 88 8 where
  quiver := ⟨-7,1,21,-6,-144,-1⟩
  word := [0,2,1,0]
  edges k := match k.val with
    | 0 => .core 18 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 2 3, quiver := ⟨7,-41,-987,6,144,-1⟩, returnVertex := 1 }
    | 2 => .core 46 ⟨12,false⟩
    | _ => .core 51 ⟨0,false⟩

def antiRow34 : CoreRow 88 8 where
  quiver := ⟨-56,-1,21,4,-3,1⟩
  word := [0,2,1,3]
  edges k := match k.val with
    | 0 => .core 52 ⟨0,false⟩
    | 1 => .boundary { kind := .unit 0 2, quiver := ⟨56,-1,-147,-4,3,-11⟩, returnVertex := 1 }
    | 2 => .core 48 ⟨4,false⟩
    | _ => .core 18 ⟨0,false⟩

def antiRow35 : CoreRow 88 8 where
  quiver := ⟨-1,11,0,-18,4,-69⟩
  word := [1,0,3,1]
  edges k := match k.val with
    | 0 => .core 37 ⟨6,false⟩
    | 1 => .core 20 ⟨0,false⟩
    | 2 => .boundary { kind := .diamond 0 3, quiver := ⟨197,-11,0,18,-1238,69⟩, returnVertex := 2 }
    | _ => .zero (4) (11) (69) (258) { phase := 0, returnVertex := 3, frame := ⟨5,true⟩, alternateTarget := 37, alternateFrame := ⟨6,false⟩ }

def antiRow36 : CoreRow 88 8 where
  quiver := ⟨6,-239,0,41,-1,44⟩
  word := [1,2,0,1]
  edges k := match k.val with
    | 0 => .zero (6) (44) (239) (1393) { phase := 0, returnVertex := 0, frame := ⟨19,false⟩, alternateTarget := 50, alternateFrame := ⟨3,false⟩ }
    | 1 => .core 21 ⟨0,false⟩
    | 2 => .boundary { kind := .diamond 0 3, quiver := ⟨-9793,239,0,-41,1803,-44⟩, returnVertex := 2 }
    | _ => .core 50 ⟨3,false⟩

def antiRow37 : CoreRow 88 8 where
  quiver := ⟨-1,-7,4,-11,0,-69⟩
  word := [1,3,1,0]
  edges k := match k.val with
    | 0 => .core 22 ⟨0,false⟩
    | 1 => .core 35 ⟨6,false⟩
    | 2 => .boundary { kind := .unit 0 1, quiver := ⟨-1,7,-479,11,-759,69⟩, returnVertex := 2 }
    | _ => .zero (4) (11) (69) (258) { phase := 1, returnVertex := 3, frame := ⟨11,true⟩, alternateTarget := 35, alternateFrame := ⟨6,false⟩ }

def antiRow38 : CoreRow 88 8 where
  quiver := ⟨-6,1,-9,-7,248,-35⟩
  word := [2,0,1,2]
  edges k := match k.val with
    | 0 => .core 53 ⟨0,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨6,-41,-9,7,-248,1701⟩, returnVertex := 1 }
    | 2 => .core 23 ⟨0,false⟩
    | _ => .boundary { kind := .unit 0 2, quiver := ⟨-2238,1,9,8673,-248,35⟩, returnVertex := 3 }

def antiRow39 : CoreRow 88 8 where
  quiver := ⟨1,-6,204,-1,44,-35⟩
  word := [2,1,0,2]
  edges k := match k.val with
    | 0 => .core 54 ⟨0,false⟩
    | 1 => .core 53 ⟨12,false⟩
    | 2 => .core 24 ⟨0,false⟩
    | _ => .boundary { kind := .unit 0 1, quiver := ⟨1,7134,-204,1539,-44,35⟩, returnVertex := 3 }

def antiRow40 : CoreRow 88 8 where
  quiver := ⟨19,-19,-2103,1,111,1⟩
  word := [2,3,0,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 2 3, quiver := ⟨-19,19,2103,-360,-39846,1⟩, returnVertex := 0 }
    | 1 => .core 25 ⟨0,false⟩
    | 2 => .core 55 ⟨0,false⟩
    | _ => .core 56 ⟨0,false⟩

def antiRow41 : CoreRow 88 8 where
  quiver := ⟨647,0,-6,-112,111,-1⟩
  word := [2,3,0,3]
  edges k := match k.val with
    | 0 => .zero (6) (112) (647) (3771) { phase := 0, returnVertex := 0, frame := ⟨12,true⟩, alternateTarget := 57, alternateFrame := ⟨0,false⟩ }
    | 1 => .boundary { kind := .diamond 0 2, quiver := ⟨-647,0,71811,112,-111,12431⟩, returnVertex := 1 }
    | 2 => .core 57 ⟨0,false⟩
    | _ => .core 25 ⟨0,false⟩

def antiRow42 : CoreRow 88 8 where
  quiver := ⟨-19,0,51,-1,1,-4⟩
  word := [2,3,1,2]
  edges k := match k.val with
    | 0 => .zero (19) (4) (51) (966) { phase := 1, returnVertex := 0, frame := ⟨13,true⟩, alternateTarget := 26, alternateFrame := ⟨0,false⟩ }
    | 1 => .core 29 ⟨3,false⟩
    | 2 => .core 26 ⟨0,false⟩
    | _ => .core 58 ⟨0,false⟩

def antiRow43 : CoreRow 88 8 where
  quiver := ⟨19,-2103,0,111,-1,112⟩
  word := [3,2,0,1]
  edges k := match k.val with
    | 0 => .zero (19) (112) (2103) (39846) { phase := 0, returnVertex := 0, frame := ⟨19,false⟩, alternateTarget := 55, alternateFrame := ⟨4,false⟩ }
    | 1 => .core 28 ⟨0,false⟩
    | 2 => .boundary { kind := .diamond 0 3, quiver := ⟨-233414,2103,0,-111,12431,-112⟩, returnVertex := 2 }
    | _ => .core 55 ⟨4,false⟩

def antiRow44 : CoreRow 88 8 where
  quiver := ⟨647,-6,6,111,1,-1⟩
  word := [3,2,0,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 3, quiver := ⟨-647,6,-6,-3771,1,35⟩, returnVertex := 0 }
    | 1 => .core 59 ⟨0,false⟩
    | 2 => .core 28 ⟨0,false⟩
    | _ => .core 57 ⟨0,false⟩

def antiRow45 : CoreRow 88 8 where
  quiver := ⟨134,-51,70,3,-1,-1⟩
  word := [3,2,1,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 3, quiver := ⟨-134,51,-70,-6831,-1,3569⟩, returnVertex := 0 }
    | 1 => .core 60 ⟨0,false⟩
    | 2 => .core 29 ⟨0,false⟩
    | _ => .core 61 ⟨0,false⟩

def antiRow46 : CoreRow 88 8 where
  quiver := ⟨1,-6,1,-1,21,-150⟩
  word := [0,1,2,0,1]
  edges k := match k.val with
    | 0 => .core 33 ⟨8,false⟩
    | 1 => .core 30 ⟨0,false⟩
    | 2 => .core 62 ⟨0,false⟩
    | _ => .core 63 ⟨0,false⟩

def antiRow47 : CoreRow 88 8 where
  quiver := ⟨-7,6,-752,-1,-21,129⟩
  word := [0,1,2,0,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨7,-6,752,41,-21,-4383⟩, returnVertex := 0 }
    | 1 => .core 64 ⟨0,false⟩
    | 2 => .core 30 ⟨0,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨-7,-97002,752,-2710,21,-129⟩, returnVertex := 3 }

def antiRow48 : CoreRow 88 8 where
  quiver := ⟨21,-60,1,-1,1,-4⟩
  word := [0,1,2,3,1]
  edges k := match k.val with
    | 0 => .core 65 ⟨0,false⟩
    | 1 => .core 31 ⟨0,false⟩
    | 2 => .core 49 ⟨2,false⟩
    | _ => .core 34 ⟨3,false⟩

def antiRow49 : CoreRow 88 8 where
  quiver := ⟨60,21,-239,-1,4,-3⟩
  word := [0,1,2,3,2,1,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 2, quiver := ⟨-60,-21,239,-1,-14336,-5022⟩, returnVertex := 0 }
    | 1 => .core 48 ⟨2,false⟩
    | 2 => .mstrip 0 (0) 2 ⟨15,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨-896,21,239,11,-4,3⟩, returnVertex := 3 }

def antiRow50 : CoreRow 88 8 where
  quiver := ⟨-239,0,6,-44,3,-1⟩
  word := [0,2,0,2,3]
  edges k := match k.val with
    | 0 => .zero (6) (44) (239) (1393) { phase := 1, returnVertex := 0, frame := ⟨12,false⟩, alternateTarget := 36, alternateFrame := ⟨4,false⟩ }
    | 1 => .boundary { kind := .fork, quiver := ⟨239,-10516,6,44,-3,131⟩, returnVertex := 1 }
    | 2 => .core 36 ⟨4,false⟩
    | _ => .core 32 ⟨0,false⟩

def antiRow51 : CoreRow 88 8 where
  quiver := ⟨3017,22,-21,-6,144,1⟩
  word := [0,2,1,0,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨-3017,-22,21,-6,-63213,-461⟩, returnVertex := 0 }
    | 1 => .boundary { kind := .fork, quiver := ⟨-3017,22,434427,6,-144,865⟩, returnVertex := 1 }
    | 2 => .core 66 ⟨0,false⟩
    | _ => .core 33 ⟨0,false⟩

def antiRow52 : CoreRow 88 8 where
  quiver := ⟨56,1,-21,4,1173,22⟩
  word := [0,2,1,3,0]
  edges k := match k.val with
    | 0 => .core 34 ⟨0,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨-56,225,65667,-4,-1173,22⟩, returnVertex := 1 }
    | 2 => .core 67 ⟨0,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨-24577,-461,21,4,-1173,-22⟩, returnVertex := 3 }

def antiRow53 : CoreRow 88 8 where
  quiver := ⟨6,-1,9,-1,248,-44⟩
  word := [2,0,1,2,0]
  edges k := match k.val with
    | 0 => .core 38 ⟨0,false⟩
    | 1 => .core 68 ⟨0,false⟩
    | 2 => .core 39 ⟨8,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨6,395,-9,10911,-248,44⟩, returnVertex := 3 }

def antiRow54 : CoreRow 88 8 where
  quiver := ⟨-1,6,-204,-7,44,1189⟩
  word := [2,1,0,2,0]
  edges k := match k.val with
    | 0 => .core 39 ⟨0,false⟩
    | 1 => .core 69 ⟨0,false⟩
    | 2 => .boundary { kind := .fork, quiver := ⟨41,-6,6930,7,44,-1189⟩, returnVertex := 2 }
    | _ => .boundary { kind := .fork, quiver := ⟨-8977,-242550,204,-7,-44,-1189⟩, returnVertex := 3 }

def antiRow55 : CoreRow 88 8 where
  quiver := ⟨0,19,-2103,-1,112,-1⟩
  word := [2,3,0,1,2]
  edges k := match k.val with
    | 0 => .zero (19) (112) (2103) (39846) { phase := 1, returnVertex := 0, frame := ⟨7,false⟩, alternateTarget := 43, alternateFrame := ⟨3,false⟩ }
    | 1 => .core 43 ⟨3,false⟩
    | 2 => .core 40 ⟨0,false⟩
    | _ => .core 70 ⟨0,false⟩

def antiRow56 : CoreRow 88 8 where
  quiver := ⟨-233414,-2122,2103,1,-111,-1⟩
  word := [2,3,0,1,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 2, quiver := ⟨233414,2122,-2103,1,490869531,4462565⟩, returnVertex := 0 }
    | 1 => .core 71 ⟨0,false⟩
    | 2 => .core 72 ⟨0,false⟩
    | _ => .core 40 ⟨0,false⟩

def antiRow57 : CoreRow 88 8 where
  quiver := ⟨647,0,-6,112,-1,1⟩
  word := [2,3,0,3,2]
  edges k := match k.val with
    | 0 => .zero (6) (112) (647) (3771) { phase := 1, returnVertex := 0, frame := ⟨12,true⟩, alternateTarget := 41, alternateFrame := ⟨0,false⟩ }
    | 1 => .core 73 ⟨0,false⟩
    | 2 => .core 41 ⟨0,false⟩
    | _ => .core 44 ⟨0,false⟩

def antiRow58 : CoreRow 88 8 where
  quiver := ⟨-19,204,-51,3,-1,4⟩
  word := [2,3,1,2,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 3, quiver := ⟨19,-204,51,3879,-1,-10400⟩, returnVertex := 0 }
    | 1 => .core 61 ⟨2,false⟩
    | 2 => .boundary { kind := .fork, quiver := ⟨-19,-204,765,-3,11,-4⟩, returnVertex := 2 }
    | _ => .core 42 ⟨0,false⟩

def antiRow59 : CoreRow 88 8 where
  quiver := ⟨-647,71811,653,-111,-1,-1⟩
  word := [3,2,0,2,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 2 3, quiver := ⟨647,-71811,-653,46461606,422490,-1⟩, returnVertex := 0 }
    | 1 => .core 44 ⟨0,false⟩
    | 2 => .core 74 ⟨0,false⟩
    | _ => .core 75 ⟨0,false⟩

def antiRow60 : CoreRow 88 8 where
  quiver := ⟨-134,351,70,-3,1,-4⟩
  word := [3,2,1,2,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨134,-351,-70,47031,9381,-4⟩, returnVertex := 0 }
    | 1 => .core 45 ⟨0,false⟩
    | 2 => .boundary { kind := .fork, quiver := ⟨919,-351,70,3,-11,4⟩, returnVertex := 2 }
    | _ => .core 76 ⟨0,false⟩

def antiRow61 : CoreRow 88 8 where
  quiver := ⟨204,19,-70,3,1,1⟩
  word := [3,2,1,2,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨-204,-19,70,3,-14279,-1329⟩, returnVertex := 0 }
    | 1 => .core 77 ⟨0,false⟩
    | 2 => .core 58 ⟨2,false⟩
    | _ => .core 45 ⟨0,false⟩

def antiRow62 : CoreRow 88 8 where
  quiver := ⟨1,6,-899,1,-129,150⟩
  word := [0,1,2,0,1,2]
  edges k := match k.val with
    | 0 => .mstrip 1 (0) 1 ⟨0,true⟩
    | 1 => .core 64 ⟨2,false⟩
    | 2 => .core 46 ⟨0,false⟩
    | _ => .boundary { kind := .unit 0 1, quiver := ⟨1,-134844,899,-19349,129,-150⟩, returnVertex := 3 }

def antiRow63 : CoreRow 88 8 where
  quiver := ⟨1,144,-1,3149,-21,150⟩
  word := [0,1,2,0,1,3]
  edges k := match k.val with
    | 0 => .core 66 ⟨9,false⟩
    | 1 => .mstrip 2 (0) 1 ⟨7,false⟩
    | 2 => .boundary { kind := .unit 0 1, quiver := ⟨1,-144,21599,-3149,472329,-150⟩, returnVertex := 2 }
    | _ => .core 46 ⟨0,false⟩

def antiRow64 : CoreRow 88 8 where
  quiver := ⟨7,-1,-899,1,21,129⟩
  word := [0,1,2,0,2,1]
  edges k := match k.val with
    | 0 => .core 78 ⟨12,false⟩
    | 1 => .core 47 ⟨0,false⟩
    | 2 => .core 62 ⟨2,false⟩
    | _ => .boundary { kind := .unit 1 2, quiver := ⟨-18872,-115972,899,1,-21,-129⟩, returnVertex := 3 }

def antiRow65 : CoreRow 88 8 where
  quiver := ⟨-21,60,-1,-1261,1,56⟩
  word := [0,1,2,3,1,0]
  edges k := match k.val with
    | 0 => .core 48 ⟨0,false⟩
    | 1 => .mstrip 3 (0) 1 ⟨10,true⟩
    | 2 => .boundary { kind := .unit 1 3, quiver := ⟨75639,-60,3359,1261,1,-56⟩, returnVertex := 2 }
    | _ => .core 67 ⟨22,false⟩

def antiRow66 : CoreRow 88 8 where
  quiver := ⟨3149,-22,1,6,144,-1⟩
  word := [0,2,1,0,3,2]
  edges k := match k.val with
    | 0 => .core 79 ⟨4,false⟩
    | 1 => .boundary { kind := .unit 2 3, quiver := ⟨-3149,18872,453457,-6,-144,-1⟩, returnVertex := 1 }
    | 2 => .core 51 ⟨0,false⟩
    | _ => .core 63 ⟨18,false⟩

def antiRow67 : CoreRow 88 8 where
  quiver := ⟨56,-1,1,-4,1261,-22⟩
  word := [0,2,1,3,0,2]
  edges k := match k.val with
    | 0 => .core 65 ⟨17,false⟩
    | 1 => .boundary { kind := .unit 0 2, quiver := ⟨-56,-1,70617,4,-1261,5022⟩, returnVertex := 1 }
    | 2 => .core 52 ⟨0,false⟩
    | _ => .core 80 ⟨12,false⟩

def antiRow68 : CoreRow 88 8 where
  quiver := ⟨-6,-1,1497,1,-248,204⟩
  word := [2,0,1,2,0,1]
  edges k := match k.val with
    | 0 => .mstrip 4 (0) 1 ⟨2,false⟩
    | 1 => .core 53 ⟨0,false⟩
    | 2 => .core 69 ⟨14,false⟩
    | _ => .boundary { kind := .unit 0 2, quiver := ⟨371250,-1,-1497,-50591,248,-204⟩, returnVertex := 3 }

def antiRow69 : CoreRow 88 8 where
  quiver := ⟨1,-1,-204,7,-44,1497⟩
  word := [2,1,0,2,0,1]
  edges k := match k.val with
    | 0 => .core 68 ⟨14,false⟩
    | 1 => .core 54 ⟨0,false⟩
    | 2 => .core 81 ⟨0,false⟩
    | _ => .boundary { kind := .unit 0 1, quiver := ⟨1,-305389,204,-65861,44,-1497⟩, returnVertex := 3 }

def antiRow70 : CoreRow 88 8 where
  quiver := ⟨-235536,19,2103,111,-112,1⟩
  word := [2,3,0,1,2,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 2 3, quiver := ⟨235536,-19,-2103,4475295,495332096,1⟩, returnVertex := 0 }
    | 1 => .boundary { kind := .fork, quiver := ⟨235536,19,-26377929,-111,112,-12431⟩, returnVertex := 1 }
    | 2 => .core 72 ⟨1,false⟩
    | _ => .core 55 ⟨0,false⟩

def antiRow71 : CoreRow 88 8 where
  quiver := ⟨233414,-2122,-25906851,-1,111,-112⟩
  word := [2,3,0,1,3,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨-233414,2122,25906851,-495304509,-6047021719203,-112⟩, returnVertex := 0 }
    | 1 => .core 56 ⟨0,false⟩
    | 2 => .core 82 ⟨0,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨-2875427047,-2122,25906851,12431,-111,112⟩, returnVertex := 3 }

def antiRow72 : CoreRow 88 8 where
  quiver := ⟨-235536,2122,-19,-1,-111,1⟩
  word := [2,3,0,1,3,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨235536,-2122,19,499807391,-111,-40317⟩, returnVertex := 0 }
    | 1 => .core 83 ⟨0,false⟩
    | 2 => .core 56 ⟨0,false⟩
    | _ => .core 70 ⟨1,false⟩

def antiRow73 : CoreRow 88 8 where
  quiver := ⟨-647,72464,-6,-112,1,-111⟩
  word := [2,3,0,3,2,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 3, quiver := ⟨647,-72464,6,46884096,1,-434895⟩, returnVertex := 0 }
    | 1 => .core 57 ⟨0,false⟩
    | 2 => .boundary { kind := .fork, quiver := ⟨8115321,-72464,-6,112,-12431,111⟩, returnVertex := 2 }
    | _ => .core 75 ⟨5,false⟩

def antiRow74 : CoreRow 88 8 where
  quiver := ⟨7970374,-71811,653,111,-112,1⟩
  word := [3,2,0,2,1,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨-7970374,71811,-653,-572360527203,-112,46892584⟩, returnVertex := 0 }
    | 1 => .boundary { kind := .fork, quiver := ⟨-7970374,884639703,653,-111,112,-12431⟩, returnVertex := 1 }
    | 2 => .core 59 ⟨0,false⟩
    | _ => .core 84 ⟨0,false⟩

def antiRow75 : CoreRow 88 8 where
  quiver := ⟨6,72464,-653,-111,1,1⟩
  word := [3,2,0,2,1,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨-6,-72464,653,-111,-3917,-47318991⟩, returnVertex := 0 }
    | 1 => .core 73 ⟨5,false⟩
    | 2 => .core 85 ⟨0,false⟩
    | _ => .core 59 ⟨0,false⟩

def antiRow76 : CoreRow 88 8 where
  quiver := ⟨-134,631,-70,1,-1,4⟩
  word := [3,2,1,2,1,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 3, quiver := ⟨134,-631,70,84555,-1,-44166⟩, returnVertex := 0 }
    | 1 => .core 77 ⟨5,false⟩
    | 2 => .core 86 ⟨0,false⟩
    | _ => .core 60 ⟨0,false⟩

def antiRow77 : CoreRow 88 8 where
  quiver := ⟨-204,631,134,-3,-1,1⟩
  word := [3,2,1,2,3,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 2 3, quiver := ⟨204,-631,-134,128721,27335,1⟩, returnVertex := 0 }
    | 1 => .core 61 ⟨0,false⟩
    | 2 => .mstrip 5 (0) 1 ⟨17,true⟩
    | _ => .core 76 ⟨5,false⟩

def antiRow78 : CoreRow 88 8 where
  quiver := ⟨-1,6,129,-7,899,-6272⟩
  word := [0,1,2,0,1,2,0,1,0]
  edges k := match k.val with
    | 0 => .mstrip 1 (0) 2 ⟨0,true⟩
    | 1 => .core 64 ⟨8,false⟩
    | 2 => .boundary { kind := .fork, quiver := ⟨41,-6,129,7,-43005,6272⟩, returnVertex := 2 }
    | _ => .boundary { kind := .unit 0 1, quiver := ⟨-1,809094,-129,5638521,-899,6272⟩, returnVertex := 3 }

def antiRow79 : CoreRow 88 8 where
  quiver := ⟨-1,-3149,22,-144,-21,-69272⟩
  word := [0,1,2,0,1,3,1,0,1]
  edges k := match k.val with
    | 0 => .core 66 ⟨3,false⟩
    | 1 => .mstrip 2 (0) 2 ⟨7,false⟩
    | 2 => .boundary { kind := .unit 0 1, quiver := ⟨-1,3149,-218137506,144,-9975189,69272⟩, returnVertex := 2 }
    | _ => .boundary { kind := .fork, quiver := ⟨461,1520835,-22,-144,21,69272⟩, returnVertex := 3 }

def antiRow80 : CoreRow 88 8 where
  quiver := ⟨-21,-27738,22,56,-1,-1261⟩
  word := [0,1,2,3,1,0,1,3,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .fork, quiver := ⟨21,27738,-22,56,461,608975⟩, returnVertex := 0 }
    | 1 => .mstrip 3 (0) 2 ⟨10,true⟩
    | 2 => .boundary { kind := .unit 1 3, quiver := ⟨-1553349,27738,-34977596,-56,-1,1261⟩, returnVertex := 2 }
    | _ => .core 67 ⟨8,false⟩

def antiRow81 : CoreRow 88 8 where
  quiver := ⟨-6,1,-204,-7,10435,-1497⟩
  word := [2,0,1,2,0,1,0,2,0]
  edges k := match k.val with
    | 0 => .mstrip 4 (0) 2 ⟨2,false⟩
    | 1 => .boundary { kind := .fork, quiver := ⟨6,-41,-204,7,-10435,71548⟩, returnVertex := 1 }
    | 2 => .core 69 ⟨0,false⟩
    | _ => .boundary { kind := .unit 0 2, quiver := ⟨-2128746,1,204,15621188,-10435,1497⟩, returnVertex := 3 }

def antiRow82 : CoreRow 88 8 where
  quiver := ⟨233414,2122,-26144515,1,-1,112⟩
  word := [2,3,0,1,3,1,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 2, quiver := ⟨-233414,-2122,26144515,1,-6102495824211,-55478660718⟩, returnVertex := 0 }
    | 1 => .core 83 ⟨2,false⟩
    | 2 => .core 71 ⟨0,false⟩
    | _ => .core 87 ⟨0,false⟩

def antiRow83 : CoreRow 88 8 where
  quiver := ⟨235536,-233414,-26144515,1,111,1⟩
  word := [2,3,0,1,3,2,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 2 3, quiver := ⟨-235536,233414,26144515,-54977399903,-6157974484929,1⟩, returnVertex := 0 }
    | 1 => .core 72 ⟨0,false⟩
    | 2 => .core 82 ⟨2,false⟩
    | _ => .mstrip 6 (0) 1 ⟨23,false⟩

def antiRow84 : CoreRow 88 8 where
  quiver := ⟨8043510,-71811,-653,-1,112,-1⟩
  word := [3,2,0,2,1,2,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 2 3, quiver := ⟨-8043510,71811,653,-577612496611,-5252411918,-1⟩, returnVertex := 0 }
    | 1 => .core 88 ⟨0,false⟩
    | 2 => .core 85 ⟨1,false⟩
    | _ => .core 74 ⟨0,false⟩

def antiRow85 : CoreRow 88 8 where
  quiver := ⟨8043510,-72464,71811,111,1,-1⟩
  word := [3,2,0,2,1,3,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 3, quiver := ⟨-8043510,72464,-71811,-582864908529,1,5203712303⟩, returnVertex := 0 }
    | 1 => .mstrip 7 (0) 1 ⟨11,true⟩
    | 2 => .core 75 ⟨0,false⟩
    | _ => .core 84 ⟨1,false⟩

def antiRow86 : CoreRow 88 8 where
  quiver := ⟨-134,-631,2454,-1,3,-4⟩
  word := [3,2,1,2,1,3,2]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 2, quiver := ⟨134,631,-2454,-1,328839,1548470⟩, returnVertex := 0 }
    | 1 => .mstrip 5 (0) 2 ⟨9,true⟩
    | 2 => .core 76 ⟨0,false⟩
    | _ => .boundary { kind := .fork, quiver := ⟨-134,9185,-2454,11,-3,4⟩, returnVertex := 3 }

def antiRow87 : CoreRow 88 8 where
  quiver := ⟨233414,-2928183558,26144515,-111,1,-112⟩
  word := [2,3,0,1,3,1,2,3]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 3, quiver := ⟨-233414,2928183558,-26144515,-683479037007123,1,76555938954884258⟩, returnVertex := 0 }
    | 1 => .mstrip 6 (0) 2 ⟨11,false⟩
    | 2 => .boundary { kind := .fork, quiver := ⟨233414,2928183558,-327930413981,111,-12431,112⟩, returnVertex := 2 }
    | _ => .core 82 ⟨0,false⟩

def antiRow88 : CoreRow 88 8 where
  quiver := ⟨-8043510,-71811,900872467,1,-112,111⟩
  word := [3,2,0,2,1,2,3,1]
  edges k := match k.val with
    | 0 => .boundary { kind := .unit 1 2, quiver := ⟨8043510,71811,-900872467,1,7246176697039058,64692552727848⟩, returnVertex := 0 }
    | 1 => .core 84 ⟨0,false⟩
    | 2 => .mstrip 7 (0) 2 ⟨15,true⟩
    | _ => .boundary { kind := .fork, quiver := ⟨100889672794,-71811,-900872467,-12431,112,-111⟩, returnVertex := 3 }

def antiStrip0 : StripRecord 88 where
  m := (3)
  a := (60)
  b := (21)
  c := (22)
  rootCore := 31
  rootQuiver := ⟨-21,-60,22,1,-1,-3⟩
  rootWord := [0,1,2,3]
  rootFrame := ⟨15,false⟩
  backward p := match p.val with
    | 0 => ⟨48,⟨20,false⟩⟩
    | 1 => ⟨16,⟨20,false⟩⟩
    | _ => ⟨49,⟨20,false⟩⟩

def antiStrip1 : StripRecord 88 where
  m := (6)
  a := (899)
  b := (129)
  c := (150)
  rootCore := 62
  rootQuiver := ⟨1,6,-899,1,-129,150⟩
  rootWord := [0,1,2,0,1,2]
  rootFrame := ⟨0,true⟩
  backward p := match p.val with
    | 0 => ⟨64,⟨2,true⟩⟩
    | 1 => ⟨46,⟨0,true⟩⟩
    | _ => ⟨78,⟨0,true⟩⟩

def antiStrip2 : StripRecord 88 where
  m := (21)
  a := (3149)
  b := (144)
  c := (150)
  rootCore := 63
  rootQuiver := ⟨1,144,-1,3149,-21,150⟩
  rootWord := [0,1,2,0,1,3]
  rootFrame := ⟨7,false⟩
  backward p := match p.val with
    | 0 => ⟨66,⟨5,false⟩⟩
    | 1 => ⟨46,⟨7,false⟩⟩
    | _ => ⟨79,⟨7,false⟩⟩

def antiStrip3 : StripRecord 88 where
  m := (21)
  a := (1261)
  b := (56)
  c := (60)
  rootCore := 65
  rootQuiver := ⟨-21,60,-1,-1261,1,56⟩
  rootWord := [0,1,2,3,1,0]
  rootFrame := ⟨10,true⟩
  backward p := match p.val with
    | 0 => ⟨67,⟨11,true⟩⟩
    | 1 => ⟨48,⟨13,true⟩⟩
    | _ => ⟨80,⟨13,true⟩⟩

def antiStrip4 : StripRecord 88 where
  m := (6)
  a := (1497)
  b := (204)
  c := (248)
  rootCore := 68
  rootQuiver := ⟨-6,-1,1497,1,-248,204⟩
  rootWord := [2,0,1,2,0,1]
  rootFrame := ⟨2,false⟩
  backward p := match p.val with
    | 0 => ⟨69,⟨8,false⟩⟩
    | 1 => ⟨53,⟨2,false⟩⟩
    | _ => ⟨81,⟨2,false⟩⟩

def antiStrip5 : StripRecord 88 where
  m := (3)
  a := (631)
  b := (134)
  c := (204)
  rootCore := 77
  rootQuiver := ⟨-204,631,134,-3,-1,1⟩
  rootWord := [3,2,1,2,3,1]
  rootFrame := ⟨17,true⟩
  backward p := match p.val with
    | 0 => ⟨76,⟨20,true⟩⟩
    | 1 => ⟨61,⟨22,true⟩⟩
    | _ => ⟨86,⟨18,true⟩⟩

def antiStrip6 : StripRecord 88 where
  m := (111)
  a := (26144515)
  b := (233414)
  c := (235536)
  rootCore := 83
  rootQuiver := ⟨235536,-233414,-26144515,1,111,1⟩
  rootWord := [2,3,0,1,3,2,1]
  rootFrame := ⟨23,false⟩
  backward p := match p.val with
    | 0 => ⟨82,⟨21,false⟩⟩
    | 1 => ⟨72,⟨23,false⟩⟩
    | _ => ⟨87,⟨19,false⟩⟩

def antiStrip7 : StripRecord 88 where
  m := (111)
  a := (8043510)
  b := (71811)
  c := (72464)
  rootCore := 85
  rootQuiver := ⟨8043510,-72464,71811,111,1,-1⟩
  rootWord := [3,2,0,2,1,3,2]
  rootFrame := ⟨11,true⟩
  backward p := match p.val with
    | 0 => ⟨84,⟨18,true⟩⟩
    | 1 => ⟨75,⟨19,true⟩⟩
    | _ => ⟨88,⟨20,true⟩⟩

def anti : Certificate where
  initial := ⟨1,6,0,1,-4,1⟩
  entryWord := []
  entryFrame := ⟨0,false⟩
  size := 88
  stripCount := 8
  core i := match i.val with
    | 0 => antiRow0
    | 1 => antiRow1
    | 2 => antiRow2
    | 3 => antiRow3
    | 4 => antiRow4
    | 5 => antiRow5
    | 6 => antiRow6
    | 7 => antiRow7
    | 8 => antiRow8
    | 9 => antiRow9
    | 10 => antiRow10
    | 11 => antiRow11
    | 12 => antiRow12
    | 13 => antiRow13
    | 14 => antiRow14
    | 15 => antiRow15
    | 16 => antiRow16
    | 17 => antiRow17
    | 18 => antiRow18
    | 19 => antiRow19
    | 20 => antiRow20
    | 21 => antiRow21
    | 22 => antiRow22
    | 23 => antiRow23
    | 24 => antiRow24
    | 25 => antiRow25
    | 26 => antiRow26
    | 27 => antiRow27
    | 28 => antiRow28
    | 29 => antiRow29
    | 30 => antiRow30
    | 31 => antiRow31
    | 32 => antiRow32
    | 33 => antiRow33
    | 34 => antiRow34
    | 35 => antiRow35
    | 36 => antiRow36
    | 37 => antiRow37
    | 38 => antiRow38
    | 39 => antiRow39
    | 40 => antiRow40
    | 41 => antiRow41
    | 42 => antiRow42
    | 43 => antiRow43
    | 44 => antiRow44
    | 45 => antiRow45
    | 46 => antiRow46
    | 47 => antiRow47
    | 48 => antiRow48
    | 49 => antiRow49
    | 50 => antiRow50
    | 51 => antiRow51
    | 52 => antiRow52
    | 53 => antiRow53
    | 54 => antiRow54
    | 55 => antiRow55
    | 56 => antiRow56
    | 57 => antiRow57
    | 58 => antiRow58
    | 59 => antiRow59
    | 60 => antiRow60
    | 61 => antiRow61
    | 62 => antiRow62
    | 63 => antiRow63
    | 64 => antiRow64
    | 65 => antiRow65
    | 66 => antiRow66
    | 67 => antiRow67
    | 68 => antiRow68
    | 69 => antiRow69
    | 70 => antiRow70
    | 71 => antiRow71
    | 72 => antiRow72
    | 73 => antiRow73
    | 74 => antiRow74
    | 75 => antiRow75
    | 76 => antiRow76
    | 77 => antiRow77
    | 78 => antiRow78
    | 79 => antiRow79
    | 80 => antiRow80
    | 81 => antiRow81
    | 82 => antiRow82
    | 83 => antiRow83
    | 84 => antiRow84
    | 85 => antiRow85
    | 86 => antiRow86
    | 87 => antiRow87
    | _ => antiRow88
  strips s := match s.val with
    | 0 => antiStrip0
    | 1 => antiStrip1
    | 2 => antiStrip2
    | 3 => antiStrip3
    | 4 => antiStrip4
    | 5 => antiStrip5
    | 6 => antiStrip6
    | _ => antiStrip7
  triangleAvoidance := true

end QuiverProofs.WitnessLStarData
