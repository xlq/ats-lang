val x = 'X'
and y = 'Y'
implement
main () = () where {
  val () = (
    print! ("print: ", 1, 2, 3); print_newline ()
  ) // end of [val]
  val () = println! ("println: ", "x = ", x, " and y = ", y)
} // end of [main]

