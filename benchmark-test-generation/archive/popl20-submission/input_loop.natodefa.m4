# EXPECT-WELL-FORMED
# EXPECT-INPUT-SEQUENCES-REACH target [ 0 ]

let failure = 42
in let complete = 42
in let x = input
in let rec loop i =
  if i == _LOOP_COUNT_
  then let target = complete in 0
  else loop (i+1)
in loop 0