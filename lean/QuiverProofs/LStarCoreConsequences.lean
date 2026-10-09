import QuiverProofs.LStarCertificate
namespace QuiverProofs.LStarCoreConsequences
open LStar RecursiveRegions TriangleRegions

theorem checked_node_NMA (c : Certificate) (h : Checks c) (i : Fin (c.size+1)) :
    ¬ MutationAcyclic (c.node i) :=
  RecursiveRegions.safe_NMA regionData regionRules (Base c)
    (fun _ hB => base_skew c hB) (checked_cyclic c h) (checked_edges c h) (safe_node c i)

theorem checked_node_triangles (c : Certificate) (h : Checks c)
    (hav : c.triangleAvoidance = true) (i : Fin (c.size+1)) (word : List (Fin 4)) :
    AllTrianglesMA (applyWord (c.node i) word) :=
  RecursiveRegions.safe_global_triangle_avoidance regionData regionRules triangleRules
    (Base c) (fun _ hB => base_skew c hB) (checked_triangles c h hav) (checked_edges c h)
    (safe_node c i) word

theorem framed_node_NMA (c : Certificate) (h : Checks c)
    (i : Fin (c.size+1)) (f : Frame) : ¬ MutationAcyclic (f.apply (c.node i)) := by
  have hn := checked_node_NMA c h i
  change ¬MutationAcyclic (CertificateSearch.transport (c.node i) f.relabeling f.flip)
  intro hm
  exact hn ((CertificateTransport.transport_MA_iff _ _ _ (c.core i).quiver.skew).mp hm)

end QuiverProofs.LStarCoreConsequences
