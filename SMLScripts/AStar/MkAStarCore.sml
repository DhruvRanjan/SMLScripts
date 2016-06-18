functor MkAStarCore(structure Table : TABLE
                    structure PQ : PQUEUE
                      where type Key.t = real) : ASTAR =
struct
  structure Set = Table.Set
  structure Seq = Set.Seq

  type weight = real
  type vertex = Set.key
  type edge = vertex * vertex * weight
  type heuristic = vertex -> real

  exception NotYetImplemented

  type graph = weight Table.table Table.table

  fun makeGraph (E : edge Seq.seq) : graph =
    let
      val tab1 = Table.collect(Seq.map(fn(a,b,c)=>(a,(b,c)))(E))
      val tab2 = Table.map(fn(a)=>Table.fromSeq(a))(tab1)
   in
      tab2
   end

  fun findPath h G (S, T) =
   let
     fun N(v) =
       case Table.find G v of
         NONE => Table.empty()
       | SOME nbr => nbr
     fun AStar D Q =
       case PQ.deleteMin Q of
         (NONE, _) => NONE
       | (SOME (a,(d,v)),Q') =>
          case Table.find D v of
            SOME _ => AStar D Q'
          | NONE =>
             if Set.find T v then SOME(v,d) else
             let
               val insert = Table.insert(fn(x,_)=>x)
               val D' = insert (v,d) D
               fun relax (q,(u,w)) = PQ.insert (d+w+h(v),(d+w,u))q
               val Q'' = Table.iter relax Q' (N v)
             in
               AStar D' Q''
             end
     val firstSeq = Seq.map(fn a => (h(a),(0.0,a)))(Set.toSeq(S))
     val firstVal = PQ.fromList(Seq.toList(firstSeq))
     val AStarVal =  AStar(Table.empty())(firstVal)
   in
     AStarVal
   end

end
