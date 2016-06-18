functor MkBoruvkaSegmenter
  (structure Seq : SEQUENCE
   structure Rand : RANDOM210
   sharing Seq = Rand.Seq)
  : SEGMENTER =
struct
  structure Seq = Rand.Seq
  open Seq

  structure R = Rand
  type vertex = int
  type weight = int
  type edge = vertex * vertex * weight

  exception NotYetImplemented
  exception error

  fun findSegments (E, n) initialCredit =
    let
      val labs = Seq.tabulate(fn i => i)(n)
      val seed1 = R.fromInt(1)
      val (bitSeq1,seed2) = R.flip(seed1)(n)
      fun minEdges(ES,l) =
        let
         val edgeSeq = Seq.tabulate(fn i => NONE)(Seq.length(l))
         fun edgeCompare((u,v,w),(u2,v2,w2))=Int.compare(w,w2)
         val sortedSeq = Seq.sort(edgeCompare)(ES)
         val revSortedSeq = Seq.rev(sortedSeq)
         val revSortedSeq' = Seq.map(fn(u,v,w)=>(Seq.nth l u,(SOME(u,v,w))))(revSortedSeq)
         val minEdgeSeq = (Seq.filter(fn(i)=>not(i=NONE))(Seq.inject revSortedSeq' edgeSeq))
        in
         minEdgeSeq
        end

       fun minStarContract(G,S,l)=
         let
          val minE = minEdges(G,l)
          val P = Seq.map(fn i =>case i of
                              (SOME(u,v,w))=>(u,v,w)
                           | _ => raise error)(minE)
          val P' = Seq.filter(fn(u,v,w)=>  ((Seq.nth S (Seq.nth l u)=1) andalso
                                            (Seq.nth S (Seq.nth l v)=0)))(P)
         in
           P'
         end

       fun MST(G,T,l,i,seed)=
        if Seq.length(G)=0 then T
        else
          let
            val (bitSeq,seed')=R.flip(seed)(n)
            val PT = minStarContract(G,bitSeq,l)
            val PT' = Seq.inject(Seq.map(fn(u,v,w)=>(Seq.nth l u,Seq.nth l v))(PT))(l)
            val P = Seq.map(Seq.nth PT')(PT')
            fun comparePL (u,v,w) =
              (Seq.nth P (Seq.nth l u)=Seq.nth l v)
            val T' = Seq.filter(fn i =>comparePL(i))(PT)
            val G' = Seq.filter(fn(u,v,w)=>not(Seq.nth P u = Seq.nth P v))(G)
          in
            MST(G',Seq.append(T,T'),P,i+1,seed')
          end
    in
      (Seq.empty(),MST(E,Seq.empty(),labs,0,seed2))
    end

end
