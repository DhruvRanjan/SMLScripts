functor MkBridges(structure STSeq : ST_SEQUENCE) : BRIDGES =
struct
  structure Seq = STSeq.Seq
  open Seq

  type vertex = int
  type edge = vertex * vertex
  type edges = edge seq

  exception NotYetImplemented

  type ugraph = vertex seq seq

  fun makeGraph (E : edge seq) : ugraph =
   let
     val s1 = collect(Int.compare)(E)
     val s2 = Seq.map(fn(a,b)=>b)(s1)
   in
     s2
   end

  fun findBridges (G : ugraph) : edges =
   let
     val seqLength = Seq.length G
     val Seq1 = Seq.tabulate(fn x => NONE)(seqLength)
     val STSeq1 = STSeq.fromSeq(Seq1)
     val nodes = Seq.tabulate(fn x => x)(seqLength)
     fun findBridges' br k j l d itr =
      let
        val jVal = STSeq.nth l j
      in
        case jVal of
          SOME(x) => (l, br, (Int.min(d,x)),itr)
        | _ => let
                val jVal2 = Seq.nth G j
                val updateSTSeq = STSeq.update (j,SOME(itr))(l)
                val adjacent = Seq.filter (fn y => if (y=k) then false else true)(jVal2)
                val (newl,newbr,newd,newitr) =
                  Seq.iter(fn(x,y)=>case x of
                  (l2,br2,d2,itr2)=>findBridges' br2 j y l2 d2 itr2)
                  (updateSTSeq,br,Seq.length(G),(itr+1))(adjacent)
                val newBridges2 = case (k>=0 andalso newd>=itr) of
                                    false => newbr
                                  | _ => Seq.append(Seq.singleton((k,j)),newbr)
               in
                 (newl,newBridges2,Int.min(newd,d),newitr)
               end
        end
     val (l,br,m,n) = Seq.iter(fn(x,y)=> case x of
                                   (a,b,c,d) => findBridges' b (~1) y a c d)
                                   (STSeq1,(Seq.empty()),(Seq.length G),0)(nodes)
   in
      br
   end

end
