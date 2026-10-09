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

theorem q179_cyclic : ∀ i, ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node i) := by
  intro i
  change Fin 89 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=27 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 ∨ i=32 ∨ i=33 ∨ i=34 ∨ i=35 ∨ i=36 ∨ i=37 ∨ i=38 ∨ i=39 ∨ i=40 ∨ i=41 ∨ i=42 ∨ i=43 ∨ i=44 ∨ i=45 ∨ i=46 ∨ i=47 ∨ i=48 ∨ i=49 ∨ i=50 ∨ i=51 ∨ i=52 ∨ i=53 ∨ i=54 ∨ i=55 ∨ i=56 ∨ i=57 ∨ i=58 ∨ i=59 ∨ i=60 ∨ i=61 ∨ i=62 ∨ i=63 ∨ i=64 ∨ i=65 ∨ i=66 ∨ i=67 ∨ i=68 ∨ i=69 ∨ i=70 ∨ i=71 ∨ i=72 ∨ i=73 ∨ i=74 ∨ i=75 ∨ i=76 ∨ i=77 ∨ i=78 ∨ i=79 ∨ i=80 ∨ i=81 ∨ i=82 ∨ i=83 ∨ i=84 ∨ i=85 ∨ i=86 ∨ i=87 ∨ i=88 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact q179_cyclic0
  · exact q179_cyclic1
  · exact q179_cyclic2
  · exact q179_cyclic3
  · exact q179_cyclic4
  · exact q179_cyclic5
  · exact q179_cyclic6
  · exact q179_cyclic7
  · exact q179_cyclic8
  · exact q179_cyclic9
  · exact q179_cyclic10
  · exact q179_cyclic11
  · exact q179_cyclic12
  · exact q179_cyclic13
  · exact q179_cyclic14
  · exact q179_cyclic15
  · exact q179_cyclic16
  · exact q179_cyclic17
  · exact q179_cyclic18
  · exact q179_cyclic19
  · exact q179_cyclic20
  · exact q179_cyclic21
  · exact q179_cyclic22
  · exact q179_cyclic23
  · exact q179_cyclic24
  · exact q179_cyclic25
  · exact q179_cyclic26
  · exact q179_cyclic27
  · exact q179_cyclic28
  · exact q179_cyclic29
  · exact q179_cyclic30
  · exact q179_cyclic31
  · exact q179_cyclic32
  · exact q179_cyclic33
  · exact q179_cyclic34
  · exact q179_cyclic35
  · exact q179_cyclic36
  · exact q179_cyclic37
  · exact q179_cyclic38
  · exact q179_cyclic39
  · exact q179_cyclic40
  · exact q179_cyclic41
  · exact q179_cyclic42
  · exact q179_cyclic43
  · exact q179_cyclic44
  · exact q179_cyclic45
  · exact q179_cyclic46
  · exact q179_cyclic47
  · exact q179_cyclic48
  · exact q179_cyclic49
  · exact q179_cyclic50
  · exact q179_cyclic51
  · exact q179_cyclic52
  · exact q179_cyclic53
  · exact q179_cyclic54
  · exact q179_cyclic55
  · exact q179_cyclic56
  · exact q179_cyclic57
  · exact q179_cyclic58
  · exact q179_cyclic59
  · exact q179_cyclic60
  · exact q179_cyclic61
  · exact q179_cyclic62
  · exact q179_cyclic63
  · exact q179_cyclic64
  · exact q179_cyclic65
  · exact q179_cyclic66
  · exact q179_cyclic67
  · exact q179_cyclic68
  · exact q179_cyclic69
  · exact q179_cyclic70
  · exact q179_cyclic71
  · exact q179_cyclic72
  · exact q179_cyclic73
  · exact q179_cyclic74
  · exact q179_cyclic75
  · exact q179_cyclic76
  · exact q179_cyclic77
  · exact q179_cyclic78
  · exact q179_cyclic79
  · exact q179_cyclic80
  · exact q179_cyclic81
  · exact q179_cyclic82
  · exact q179_cyclic83
  · exact q179_cyclic84
  · exact q179_cyclic85
  · exact q179_cyclic86
  · exact q179_cyclic87
  · exact q179_cyclic88

end QuiverProofs.BoundedLStarChecks
