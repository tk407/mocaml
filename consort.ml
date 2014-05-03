

let comparator i1 i2 lo hi = (boxc (( (fun _ -> map_mvar i1 (fun x -> ((E_comp (fun _ -> (map_mvar i2 (fun y -> (E_comp (fun _ ->
                  if x < y then (((boxe (put_mvar lo x)) >>= func 1 tunit (boxe (put_mvar hi y))))
                           else (((boxe (put_mvar lo y)) >>= func 1 tunit (boxe (put_mvar hi x))))
 ))))))))))))

let rec make_network xs = let rec make_column l = (match l with 
              | x0::x1::[] -> let r0 = make_mvar () in 
                              let r1 = make_mvar () in
                              (r0 , [ r1 ], [ comparator x0 x1 r0 r1 ] )
              |  x0::x1::t -> let r0 = make_mvar () in 
                              let r1 = make_mvar () in
                              let c0 = comparator x0 x1 r0 r1 in 
                              let (rn, rl, cl) = make_column (r0::t) in 
                              (rn, r1::rl, c0::cl)
              | _ -> assert false) in
              (match xs with 
               | x0::x1::[] -> let r0 = make_mvar () in 
                               let r1 = make_mvar () in
                               ([r0; r1 ], [ comparator x0 x1 r0 r1 ] )
               | x0::x1::t -> let (rn, rl, cl) = make_column (x0::x1::t) in
                              let (rs, comps) = make_network rl in
                              (rn :: rs, List.append cl comps)
               | _ -> assert false)

let consort l = let n = length l in 
                let xs = map (fun _ -> make_mvar () ) l in
                let _ = map (fun (k, x) -> Queue.add k x.v) (combine l xs) in 
                let (rs, comps) = (make_network xs) in 
                let start = match comps with 
                            | c :: [] -> (boxe c)
                            | _ -> (boxe (joinN (comps))) in
                (start >>= func 2 tunit (E_comp (fun _ -> ((map (fun i -> printmvar i "\n" ) rs); cunit)))) 
                

let comptest a b = let x0 = make_mvar () in
                   let x1 = make_mvar () in 
                   let r0 = make_mvar () in
                   let r1 = make_mvar () in
                   let _ = Queue.add a x0.v in 
                   let _ = Queue.add b x1.v in
                   (x0, x1, r0, r1, (comparator x0 x1 r0 r1) >>= func 7 tunit cunit)
                
