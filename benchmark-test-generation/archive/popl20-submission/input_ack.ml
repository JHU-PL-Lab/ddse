
let xi = 2
in let yi = 1
in let rec ack m n =
     if m == 0
     then 
       n+1
     else 
     if n == 0
     then 
       ack (m-1) 1 
     else 
       let _ = 0 in 
       ack (m-1) (ack m (n-1))
in 
let _ =
  if 0 <= xi && 0 <= yi
  then 
    ack xi yi
  else 0
in let _ = 
     assert (ack 2 1 = 5);()
in 0
;;