functor MkAllShortestPaths (Table : TABLE) : ALL_SHORTEST_PATHS =
struct
  open Table
  open Seq

  exception NotYetImplemented
  type nyi = unit

  (* Table.key defines our vertex type *)
  type vertex = key
  type edge = vertex * vertex

  type graph = vertex Seq.seq Table.table
  (*type asp = (graph * vertex * (int Table.table))*)
  type asp = set Table.table

  fun makeGraph (E : edge seq) : graph =
      Table.collect E

  fun numEdges (G : graph) : int =
      Table.iter (fn(a,(b,c)) => Seq.length(c)+a)(0)(G)

  fun numVertices (G : graph) : int =
    let
      val SeqKeys = Table.domain G
      val SeqSeqs = Table.range G
      val SeqSeqs2 = Set.fromSeq(Seq.flatten SeqSeqs)
    in
      Set.size(Set.union(SeqKeys,SeqSeqs2))
    end

  exception error

  fun outNeighbors (G : graph) (v : vertex) : vertex seq =
      case Table.find G v of
        SOME(x) => x
            | _ => Seq.empty()

  fun makeASP (G : graph) (v : vertex) : asp =
    case Table.find G v of
       NONE => Table.empty()
     | SOME _ =>
           let
             fun reachable(node,depth,A,X) =
               case Seq.length(outNeighbors(G)(node)) of
                  0 => A
                | _ =>
                    let
                      val frontier =
           Seq.filter (fn y => not (Table.Set.find X y)) (outNeighbors G node)
                      val parentMap =
           Seq.map(fn y => (y, ((Table.Set.singleton node), depth)))(frontier)
                      val f =
                 fn ((x,d1),(y,d2)) => case Int.compare(d1,d2) of
                                        LESS => (x,d1)
                                      | GREATER => (y,d2)
                                      | _ => (Table.Set.union(x,y),d1)
                      val new = Table.merge(f)(A,Table.fromSeq(parentMap))
                      val newX = Table.Set.union(X,Table.Set.fromSeq(frontier))
                      val frontier2 =
                     Seq.map(fn y => reachable(y,depth+1,new,newX))(frontier)
                    in
                      Seq.reduce(Table.merge f)(Table.empty())(frontier2)
                    end
             val aspWithDepths =
           reachable(v,0,$(v,(Table.Set.singleton v,0)),Table.Set.singleton(v))
             val aspWithoutDepths = Table.map(fn(a,b)=>a)(aspWithDepths)
          in
            aspWithoutDepths
          end

  fun report (A : asp) (v : vertex) : vertex seq seq =
      case Table.find A v of
         NONE => Seq.empty()
       | SOME(x) =>
         if (Table.Key.equal(v, Seq.nth(Table.Set.toSeq(x)) 0) andalso
              (Table.Set.size x = 1)) then
              Seq.singleton(Seq.singleton(v))
           else
             let
               val path = Table.Set.toSeq(x)
               val path2 = flatten(map(fn i => report A i)(path))
               val path3 = map(fn i => Seq.append(i,Seq.singleton(v)))(path2)
             in
               path3
             end

end
