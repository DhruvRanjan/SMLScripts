functor MkDivideAndConquerPD (structure P : PAREN_PACKAGE) : PAREN_DIST =
struct
  structure P = P
  open Primitives
  open P
  open Seq

     fun parenDist (parens : paren seq) : int option =
         let
            fun max (_,_,a,b,c)=
              if a>b then
                     (if a > c then a else c)
              else if b > c then b else c
            fun pm s =
              case showt s of
                 EMPTY => (0,0,0,0,0)
               | ELT OPAREN => (0,1,1,0,0)
               | ELT CPAREN => (1,0,0,1,0)
               | NODE(l,r) =>
                    let
                      val ((a,b,c,d,e),(f,g,h,i,j)) =
                          par (fn () => pm l, fn () => pm r)
                      in
                        let
                          val (k,z) = if b > f then (a,g+b-f)
                                      else (a+f-b,g)
                          val (m,n) = if c > i then (c,length(r)+c)
                                      else (i,i)
                          val p = if b > f then c+i-(b-f)
                                  else c+i-(f-b)
                        in
                          (k,z,m,n,p)
                        end
                    end
           in
             SOME(max(pm(parens)))
           end

end
