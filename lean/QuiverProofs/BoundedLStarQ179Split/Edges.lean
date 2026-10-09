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

theorem q179_edges : ∀ i k, EdgeChecks BoundedLStarData.q179 i k ((BoundedLStarData.q179.core i).edges k) := by
  intro i k
  change Fin 89 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=27 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 ∨ i=32 ∨ i=33 ∨ i=34 ∨ i=35 ∨ i=36 ∨ i=37 ∨ i=38 ∨ i=39 ∨ i=40 ∨ i=41 ∨ i=42 ∨ i=43 ∨ i=44 ∨ i=45 ∨ i=46 ∨ i=47 ∨ i=48 ∨ i=49 ∨ i=50 ∨ i=51 ∨ i=52 ∨ i=53 ∨ i=54 ∨ i=55 ∨ i=56 ∨ i=57 ∨ i=58 ∨ i=59 ∨ i=60 ∨ i=61 ∨ i=62 ∨ i=63 ∨ i=64 ∨ i=65 ∨ i=66 ∨ i=67 ∨ i=68 ∨ i=69 ∨ i=70 ∨ i=71 ∨ i=72 ∨ i=73 ∨ i=74 ∨ i=75 ∨ i=76 ∨ i=77 ∨ i=78 ∨ i=79 ∨ i=80 ∨ i=81 ∨ i=82 ∨ i=83 ∨ i=84 ∨ i=85 ∨ i=86 ∨ i=87 ∨ i=88 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge0_0
    · exact q179_edge0_1
    · exact q179_edge0_2
    · exact q179_edge0_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge1_0
    · exact q179_edge1_1
    · exact q179_edge1_2
    · exact q179_edge1_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge2_0
    · exact q179_edge2_1
    · exact q179_edge2_2
    · exact q179_edge2_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge3_0
    · exact q179_edge3_1
    · exact q179_edge3_2
    · exact q179_edge3_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge4_0
    · exact q179_edge4_1
    · exact q179_edge4_2
    · exact q179_edge4_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge5_0
    · exact q179_edge5_1
    · exact q179_edge5_2
    · exact q179_edge5_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge6_0
    · exact q179_edge6_1
    · exact q179_edge6_2
    · exact q179_edge6_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge7_0
    · exact q179_edge7_1
    · exact q179_edge7_2
    · exact q179_edge7_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge8_0
    · exact q179_edge8_1
    · exact q179_edge8_2
    · exact q179_edge8_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge9_0
    · exact q179_edge9_1
    · exact q179_edge9_2
    · exact q179_edge9_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge10_0
    · exact q179_edge10_1
    · exact q179_edge10_2
    · exact q179_edge10_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge11_0
    · exact q179_edge11_1
    · exact q179_edge11_2
    · exact q179_edge11_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge12_0
    · exact q179_edge12_1
    · exact q179_edge12_2
    · exact q179_edge12_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge13_0
    · exact q179_edge13_1
    · exact q179_edge13_2
    · exact q179_edge13_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge14_0
    · exact q179_edge14_1
    · exact q179_edge14_2
    · exact q179_edge14_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge15_0
    · exact q179_edge15_1
    · exact q179_edge15_2
    · exact q179_edge15_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge16_0
    · exact q179_edge16_1
    · exact q179_edge16_2
    · exact q179_edge16_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge17_0
    · exact q179_edge17_1
    · exact q179_edge17_2
    · exact q179_edge17_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge18_0
    · exact q179_edge18_1
    · exact q179_edge18_2
    · exact q179_edge18_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge19_0
    · exact q179_edge19_1
    · exact q179_edge19_2
    · exact q179_edge19_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge20_0
    · exact q179_edge20_1
    · exact q179_edge20_2
    · exact q179_edge20_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge21_0
    · exact q179_edge21_1
    · exact q179_edge21_2
    · exact q179_edge21_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge22_0
    · exact q179_edge22_1
    · exact q179_edge22_2
    · exact q179_edge22_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge23_0
    · exact q179_edge23_1
    · exact q179_edge23_2
    · exact q179_edge23_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge24_0
    · exact q179_edge24_1
    · exact q179_edge24_2
    · exact q179_edge24_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge25_0
    · exact q179_edge25_1
    · exact q179_edge25_2
    · exact q179_edge25_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge26_0
    · exact q179_edge26_1
    · exact q179_edge26_2
    · exact q179_edge26_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge27_0
    · exact q179_edge27_1
    · exact q179_edge27_2
    · exact q179_edge27_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge28_0
    · exact q179_edge28_1
    · exact q179_edge28_2
    · exact q179_edge28_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge29_0
    · exact q179_edge29_1
    · exact q179_edge29_2
    · exact q179_edge29_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge30_0
    · exact q179_edge30_1
    · exact q179_edge30_2
    · exact q179_edge30_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge31_0
    · exact q179_edge31_1
    · exact q179_edge31_2
    · exact q179_edge31_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge32_0
    · exact q179_edge32_1
    · exact q179_edge32_2
    · exact q179_edge32_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge33_0
    · exact q179_edge33_1
    · exact q179_edge33_2
    · exact q179_edge33_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge34_0
    · exact q179_edge34_1
    · exact q179_edge34_2
    · exact q179_edge34_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge35_0
    · exact q179_edge35_1
    · exact q179_edge35_2
    · exact q179_edge35_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge36_0
    · exact q179_edge36_1
    · exact q179_edge36_2
    · exact q179_edge36_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge37_0
    · exact q179_edge37_1
    · exact q179_edge37_2
    · exact q179_edge37_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge38_0
    · exact q179_edge38_1
    · exact q179_edge38_2
    · exact q179_edge38_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge39_0
    · exact q179_edge39_1
    · exact q179_edge39_2
    · exact q179_edge39_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge40_0
    · exact q179_edge40_1
    · exact q179_edge40_2
    · exact q179_edge40_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge41_0
    · exact q179_edge41_1
    · exact q179_edge41_2
    · exact q179_edge41_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge42_0
    · exact q179_edge42_1
    · exact q179_edge42_2
    · exact q179_edge42_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge43_0
    · exact q179_edge43_1
    · exact q179_edge43_2
    · exact q179_edge43_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge44_0
    · exact q179_edge44_1
    · exact q179_edge44_2
    · exact q179_edge44_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge45_0
    · exact q179_edge45_1
    · exact q179_edge45_2
    · exact q179_edge45_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge46_0
    · exact q179_edge46_1
    · exact q179_edge46_2
    · exact q179_edge46_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge47_0
    · exact q179_edge47_1
    · exact q179_edge47_2
    · exact q179_edge47_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge48_0
    · exact q179_edge48_1
    · exact q179_edge48_2
    · exact q179_edge48_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge49_0
    · exact q179_edge49_1
    · exact q179_edge49_2
    · exact q179_edge49_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge50_0
    · exact q179_edge50_1
    · exact q179_edge50_2
    · exact q179_edge50_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge51_0
    · exact q179_edge51_1
    · exact q179_edge51_2
    · exact q179_edge51_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge52_0
    · exact q179_edge52_1
    · exact q179_edge52_2
    · exact q179_edge52_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge53_0
    · exact q179_edge53_1
    · exact q179_edge53_2
    · exact q179_edge53_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge54_0
    · exact q179_edge54_1
    · exact q179_edge54_2
    · exact q179_edge54_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge55_0
    · exact q179_edge55_1
    · exact q179_edge55_2
    · exact q179_edge55_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge56_0
    · exact q179_edge56_1
    · exact q179_edge56_2
    · exact q179_edge56_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge57_0
    · exact q179_edge57_1
    · exact q179_edge57_2
    · exact q179_edge57_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge58_0
    · exact q179_edge58_1
    · exact q179_edge58_2
    · exact q179_edge58_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge59_0
    · exact q179_edge59_1
    · exact q179_edge59_2
    · exact q179_edge59_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge60_0
    · exact q179_edge60_1
    · exact q179_edge60_2
    · exact q179_edge60_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge61_0
    · exact q179_edge61_1
    · exact q179_edge61_2
    · exact q179_edge61_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge62_0
    · exact q179_edge62_1
    · exact q179_edge62_2
    · exact q179_edge62_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge63_0
    · exact q179_edge63_1
    · exact q179_edge63_2
    · exact q179_edge63_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge64_0
    · exact q179_edge64_1
    · exact q179_edge64_2
    · exact q179_edge64_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge65_0
    · exact q179_edge65_1
    · exact q179_edge65_2
    · exact q179_edge65_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge66_0
    · exact q179_edge66_1
    · exact q179_edge66_2
    · exact q179_edge66_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge67_0
    · exact q179_edge67_1
    · exact q179_edge67_2
    · exact q179_edge67_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge68_0
    · exact q179_edge68_1
    · exact q179_edge68_2
    · exact q179_edge68_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge69_0
    · exact q179_edge69_1
    · exact q179_edge69_2
    · exact q179_edge69_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge70_0
    · exact q179_edge70_1
    · exact q179_edge70_2
    · exact q179_edge70_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge71_0
    · exact q179_edge71_1
    · exact q179_edge71_2
    · exact q179_edge71_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge72_0
    · exact q179_edge72_1
    · exact q179_edge72_2
    · exact q179_edge72_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge73_0
    · exact q179_edge73_1
    · exact q179_edge73_2
    · exact q179_edge73_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge74_0
    · exact q179_edge74_1
    · exact q179_edge74_2
    · exact q179_edge74_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge75_0
    · exact q179_edge75_1
    · exact q179_edge75_2
    · exact q179_edge75_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge76_0
    · exact q179_edge76_1
    · exact q179_edge76_2
    · exact q179_edge76_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge77_0
    · exact q179_edge77_1
    · exact q179_edge77_2
    · exact q179_edge77_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge78_0
    · exact q179_edge78_1
    · exact q179_edge78_2
    · exact q179_edge78_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge79_0
    · exact q179_edge79_1
    · exact q179_edge79_2
    · exact q179_edge79_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge80_0
    · exact q179_edge80_1
    · exact q179_edge80_2
    · exact q179_edge80_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge81_0
    · exact q179_edge81_1
    · exact q179_edge81_2
    · exact q179_edge81_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge82_0
    · exact q179_edge82_1
    · exact q179_edge82_2
    · exact q179_edge82_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge83_0
    · exact q179_edge83_1
    · exact q179_edge83_2
    · exact q179_edge83_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge84_0
    · exact q179_edge84_1
    · exact q179_edge84_2
    · exact q179_edge84_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge85_0
    · exact q179_edge85_1
    · exact q179_edge85_2
    · exact q179_edge85_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge86_0
    · exact q179_edge86_1
    · exact q179_edge86_2
    · exact q179_edge86_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge87_0
    · exact q179_edge87_1
    · exact q179_edge87_2
    · exact q179_edge87_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q179_edge88_0
    · exact q179_edge88_1
    · exact q179_edge88_2
    · exact q179_edge88_3

end QuiverProofs.BoundedLStarChecks
