import QuiverProofs.BoundedLStarQ179Split.Nodes00
import QuiverProofs.BoundedLStarQ179Split.Nodes01
import QuiverProofs.BoundedLStarQ179Split.Nodes02
import QuiverProofs.BoundedLStarQ179Split.Nodes03
import QuiverProofs.BoundedLStarQ179Split.Nodes04
import QuiverProofs.BoundedLStarQ179Split.Nodes05
import QuiverProofs.BoundedLStarQ179Split.Nodes06
import QuiverProofs.BoundedLStarQ179Split.Nodes07
import QuiverProofs.BoundedLStarQ179Split.Nodes08
import QuiverProofs.BoundedLStarQ179Split.Nodes09
import QuiverProofs.BoundedLStarQ179Split.Nodes10
import QuiverProofs.BoundedLStarQ179Split.Nodes11
import QuiverProofs.BoundedLStarQ179Split.Nodes12
import QuiverProofs.BoundedLStarQ179Split.Nodes13
import QuiverProofs.BoundedLStarQ179Split.Nodes14
import QuiverProofs.BoundedLStarQ179Split.Nodes15
import QuiverProofs.BoundedLStarQ179Split.Nodes16
import QuiverProofs.BoundedLStarQ179Split.Nodes17
import QuiverProofs.BoundedLStarQ179Split.Nodes18
import QuiverProofs.BoundedLStarQ179Split.Nodes19
import QuiverProofs.BoundedLStarQ179Split.Nodes20
import QuiverProofs.BoundedLStarQ179Split.Nodes21
import QuiverProofs.BoundedLStarQ179Split.Nodes22
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_triangles : ∀ i, TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node i) = true := by
  intro i
  change Fin 89 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=27 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 ∨ i=32 ∨ i=33 ∨ i=34 ∨ i=35 ∨ i=36 ∨ i=37 ∨ i=38 ∨ i=39 ∨ i=40 ∨ i=41 ∨ i=42 ∨ i=43 ∨ i=44 ∨ i=45 ∨ i=46 ∨ i=47 ∨ i=48 ∨ i=49 ∨ i=50 ∨ i=51 ∨ i=52 ∨ i=53 ∨ i=54 ∨ i=55 ∨ i=56 ∨ i=57 ∨ i=58 ∨ i=59 ∨ i=60 ∨ i=61 ∨ i=62 ∨ i=63 ∨ i=64 ∨ i=65 ∨ i=66 ∨ i=67 ∨ i=68 ∨ i=69 ∨ i=70 ∨ i=71 ∨ i=72 ∨ i=73 ∨ i=74 ∨ i=75 ∨ i=76 ∨ i=77 ∨ i=78 ∨ i=79 ∨ i=80 ∨ i=81 ∨ i=82 ∨ i=83 ∨ i=84 ∨ i=85 ∨ i=86 ∨ i=87 ∨ i=88 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact q179_triangles0
  · exact q179_triangles1
  · exact q179_triangles2
  · exact q179_triangles3
  · exact q179_triangles4
  · exact q179_triangles5
  · exact q179_triangles6
  · exact q179_triangles7
  · exact q179_triangles8
  · exact q179_triangles9
  · exact q179_triangles10
  · exact q179_triangles11
  · exact q179_triangles12
  · exact q179_triangles13
  · exact q179_triangles14
  · exact q179_triangles15
  · exact q179_triangles16
  · exact q179_triangles17
  · exact q179_triangles18
  · exact q179_triangles19
  · exact q179_triangles20
  · exact q179_triangles21
  · exact q179_triangles22
  · exact q179_triangles23
  · exact q179_triangles24
  · exact q179_triangles25
  · exact q179_triangles26
  · exact q179_triangles27
  · exact q179_triangles28
  · exact q179_triangles29
  · exact q179_triangles30
  · exact q179_triangles31
  · exact q179_triangles32
  · exact q179_triangles33
  · exact q179_triangles34
  · exact q179_triangles35
  · exact q179_triangles36
  · exact q179_triangles37
  · exact q179_triangles38
  · exact q179_triangles39
  · exact q179_triangles40
  · exact q179_triangles41
  · exact q179_triangles42
  · exact q179_triangles43
  · exact q179_triangles44
  · exact q179_triangles45
  · exact q179_triangles46
  · exact q179_triangles47
  · exact q179_triangles48
  · exact q179_triangles49
  · exact q179_triangles50
  · exact q179_triangles51
  · exact q179_triangles52
  · exact q179_triangles53
  · exact q179_triangles54
  · exact q179_triangles55
  · exact q179_triangles56
  · exact q179_triangles57
  · exact q179_triangles58
  · exact q179_triangles59
  · exact q179_triangles60
  · exact q179_triangles61
  · exact q179_triangles62
  · exact q179_triangles63
  · exact q179_triangles64
  · exact q179_triangles65
  · exact q179_triangles66
  · exact q179_triangles67
  · exact q179_triangles68
  · exact q179_triangles69
  · exact q179_triangles70
  · exact q179_triangles71
  · exact q179_triangles72
  · exact q179_triangles73
  · exact q179_triangles74
  · exact q179_triangles75
  · exact q179_triangles76
  · exact q179_triangles77
  · exact q179_triangles78
  · exact q179_triangles79
  · exact q179_triangles80
  · exact q179_triangles81
  · exact q179_triangles82
  · exact q179_triangles83
  · exact q179_triangles84
  · exact q179_triangles85
  · exact q179_triangles86
  · exact q179_triangles87
  · exact q179_triangles88

end QuiverProofs.BoundedLStarChecks
