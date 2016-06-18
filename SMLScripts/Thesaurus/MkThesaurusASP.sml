functor MkThesaurusASP (ASP : ALL_SHORTEST_PATHS where type vertex = string)
  : THESAURUS =
struct
  structure Seq = ASP.Seq
  open Seq
  
  exception NotYetImplemented
  type nyi = unit

  type thesaurus = ASP.graph

  fun make (S : (string * string seq) seq) : thesaurus =
      ASP.makeGraph (flatten (map (fn (a,b) => map (fn c => (a,c)) b) S))

  fun numWords (T : thesaurus) : int = ASP.numVertices T

  fun synonyms (T : thesaurus) (w : string) : string seq =
    ASP.outNeighbors T w

  fun query (T : thesaurus) (w1 : string) : (string -> string seq seq) =
      let
        val aspVal = ASP.makeASP T w1
      in
        (fn a => ASP.report aspVal a)
      end

end
