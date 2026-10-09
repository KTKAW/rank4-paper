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

theorem q179_reachable : ∀ i, EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core i).word) (BoundedLStarData.q179.node i) := by
  intro i
  change Fin 89 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=27 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 ∨ i=32 ∨ i=33 ∨ i=34 ∨ i=35 ∨ i=36 ∨ i=37 ∨ i=38 ∨ i=39 ∨ i=40 ∨ i=41 ∨ i=42 ∨ i=43 ∨ i=44 ∨ i=45 ∨ i=46 ∨ i=47 ∨ i=48 ∨ i=49 ∨ i=50 ∨ i=51 ∨ i=52 ∨ i=53 ∨ i=54 ∨ i=55 ∨ i=56 ∨ i=57 ∨ i=58 ∨ i=59 ∨ i=60 ∨ i=61 ∨ i=62 ∨ i=63 ∨ i=64 ∨ i=65 ∨ i=66 ∨ i=67 ∨ i=68 ∨ i=69 ∨ i=70 ∨ i=71 ∨ i=72 ∨ i=73 ∨ i=74 ∨ i=75 ∨ i=76 ∨ i=77 ∨ i=78 ∨ i=79 ∨ i=80 ∨ i=81 ∨ i=82 ∨ i=83 ∨ i=84 ∨ i=85 ∨ i=86 ∨ i=87 ∨ i=88 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact q179_reachable0
  · exact q179_reachable1
  · exact q179_reachable2
  · exact q179_reachable3
  · exact q179_reachable4
  · exact q179_reachable5
  · exact q179_reachable6
  · exact q179_reachable7
  · exact q179_reachable8
  · exact q179_reachable9
  · exact q179_reachable10
  · exact q179_reachable11
  · exact q179_reachable12
  · exact q179_reachable13
  · exact q179_reachable14
  · exact q179_reachable15
  · exact q179_reachable16
  · exact q179_reachable17
  · exact q179_reachable18
  · exact q179_reachable19
  · exact q179_reachable20
  · exact q179_reachable21
  · exact q179_reachable22
  · exact q179_reachable23
  · exact q179_reachable24
  · exact q179_reachable25
  · exact q179_reachable26
  · exact q179_reachable27
  · exact q179_reachable28
  · exact q179_reachable29
  · exact q179_reachable30
  · exact q179_reachable31
  · exact q179_reachable32
  · exact q179_reachable33
  · exact q179_reachable34
  · exact q179_reachable35
  · exact q179_reachable36
  · exact q179_reachable37
  · exact q179_reachable38
  · exact q179_reachable39
  · exact q179_reachable40
  · exact q179_reachable41
  · exact q179_reachable42
  · exact q179_reachable43
  · exact q179_reachable44
  · exact q179_reachable45
  · exact q179_reachable46
  · exact q179_reachable47
  · exact q179_reachable48
  · exact q179_reachable49
  · exact q179_reachable50
  · exact q179_reachable51
  · exact q179_reachable52
  · exact q179_reachable53
  · exact q179_reachable54
  · exact q179_reachable55
  · exact q179_reachable56
  · exact q179_reachable57
  · exact q179_reachable58
  · exact q179_reachable59
  · exact q179_reachable60
  · exact q179_reachable61
  · exact q179_reachable62
  · exact q179_reachable63
  · exact q179_reachable64
  · exact q179_reachable65
  · exact q179_reachable66
  · exact q179_reachable67
  · exact q179_reachable68
  · exact q179_reachable69
  · exact q179_reachable70
  · exact q179_reachable71
  · exact q179_reachable72
  · exact q179_reachable73
  · exact q179_reachable74
  · exact q179_reachable75
  · exact q179_reachable76
  · exact q179_reachable77
  · exact q179_reachable78
  · exact q179_reachable79
  · exact q179_reachable80
  · exact q179_reachable81
  · exact q179_reachable82
  · exact q179_reachable83
  · exact q179_reachable84
  · exact q179_reachable85
  · exact q179_reachable86
  · exact q179_reachable87
  · exact q179_reachable88

end QuiverProofs.BoundedLStarChecks
