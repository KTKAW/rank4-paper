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

theorem q179_descents : ∀ i, allTriangleDescentsCheck (BoundedLStarData.q179.node i) = true := by
  intro i
  change Fin 89 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=27 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 ∨ i=32 ∨ i=33 ∨ i=34 ∨ i=35 ∨ i=36 ∨ i=37 ∨ i=38 ∨ i=39 ∨ i=40 ∨ i=41 ∨ i=42 ∨ i=43 ∨ i=44 ∨ i=45 ∨ i=46 ∨ i=47 ∨ i=48 ∨ i=49 ∨ i=50 ∨ i=51 ∨ i=52 ∨ i=53 ∨ i=54 ∨ i=55 ∨ i=56 ∨ i=57 ∨ i=58 ∨ i=59 ∨ i=60 ∨ i=61 ∨ i=62 ∨ i=63 ∨ i=64 ∨ i=65 ∨ i=66 ∨ i=67 ∨ i=68 ∨ i=69 ∨ i=70 ∨ i=71 ∨ i=72 ∨ i=73 ∨ i=74 ∨ i=75 ∨ i=76 ∨ i=77 ∨ i=78 ∨ i=79 ∨ i=80 ∨ i=81 ∨ i=82 ∨ i=83 ∨ i=84 ∨ i=85 ∨ i=86 ∨ i=87 ∨ i=88 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact q179_descent0
  · exact q179_descent1
  · exact q179_descent2
  · exact q179_descent3
  · exact q179_descent4
  · exact q179_descent5
  · exact q179_descent6
  · exact q179_descent7
  · exact q179_descent8
  · exact q179_descent9
  · exact q179_descent10
  · exact q179_descent11
  · exact q179_descent12
  · exact q179_descent13
  · exact q179_descent14
  · exact q179_descent15
  · exact q179_descent16
  · exact q179_descent17
  · exact q179_descent18
  · exact q179_descent19
  · exact q179_descent20
  · exact q179_descent21
  · exact q179_descent22
  · exact q179_descent23
  · exact q179_descent24
  · exact q179_descent25
  · exact q179_descent26
  · exact q179_descent27
  · exact q179_descent28
  · exact q179_descent29
  · exact q179_descent30
  · exact q179_descent31
  · exact q179_descent32
  · exact q179_descent33
  · exact q179_descent34
  · exact q179_descent35
  · exact q179_descent36
  · exact q179_descent37
  · exact q179_descent38
  · exact q179_descent39
  · exact q179_descent40
  · exact q179_descent41
  · exact q179_descent42
  · exact q179_descent43
  · exact q179_descent44
  · exact q179_descent45
  · exact q179_descent46
  · exact q179_descent47
  · exact q179_descent48
  · exact q179_descent49
  · exact q179_descent50
  · exact q179_descent51
  · exact q179_descent52
  · exact q179_descent53
  · exact q179_descent54
  · exact q179_descent55
  · exact q179_descent56
  · exact q179_descent57
  · exact q179_descent58
  · exact q179_descent59
  · exact q179_descent60
  · exact q179_descent61
  · exact q179_descent62
  · exact q179_descent63
  · exact q179_descent64
  · exact q179_descent65
  · exact q179_descent66
  · exact q179_descent67
  · exact q179_descent68
  · exact q179_descent69
  · exact q179_descent70
  · exact q179_descent71
  · exact q179_descent72
  · exact q179_descent73
  · exact q179_descent74
  · exact q179_descent75
  · exact q179_descent76
  · exact q179_descent77
  · exact q179_descent78
  · exact q179_descent79
  · exact q179_descent80
  · exact q179_descent81
  · exact q179_descent82
  · exact q179_descent83
  · exact q179_descent84
  · exact q179_descent85
  · exact q179_descent86
  · exact q179_descent87
  · exact q179_descent88

end QuiverProofs.BoundedLStarChecks
