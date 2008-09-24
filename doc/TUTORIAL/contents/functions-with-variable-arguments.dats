//
//
// Author: Hongwei Xi (August, 2007)
//
//

#define N 9

implement main (argc, argv) = let

// [loop1] and [loop2] are verified to be terminating based on the supplied metrics

// [.< N-i, 0 >.] is a termination metric
// Ignore it if you have not learned this feature yet
fun loop1 {i: nat | i <= N} .< N-i, 0 >. (i: int i): void =
  if i < N then loop2 (i+1, i+1) else ()

// [.< N-i, N+1-j >.] is a termination metric
// Ignore it if you have notlearned this feature yet
and loop2 {i,j:nat | i <= N; j <= N+1} .< N-i, N+2-j >. (i: int i, j: int j): void =
  if j <= N then begin
    if (i < j) then print '\t';
    printf ("%1d*%1d=%2.2d", @(i, j, i * j));
    loop2 (i, j+1)
  end else begin
    print_newline (); loop1 (i)
  end

in
  loop1 (0) 
end // end of [main]
