/*
** HFUSE: FUSE file system (modular) for AWS S3
** Mark Reynolds
*/

(* ****** ****** *)

(*
** HX-2010-10-01: adapting Mark's C code to ATS
*)

(* ****** ****** *)

staload "libc/SATS/errno.sats"
staload "libc/SATS/printf.sats"
staload "libc/SATS/stdarg.sats"
staload "libc/SATS/stdio.sats"
staload "libc/sys/SATS/types.sats"

(* ****** ****** *)

staload "hfuse.sats"

(* ****** ****** *)

/*
static int tfprintf(const char *fmt, ...)
{
  va_list ap;
  FILE *fout;
  int   r = 0;

  pthread_mutex_lock(&mutex);
  va_start(ap, fmt);
  fout = fopen("/var/log/hfuselog", "a+");
  if ( fout != NULL )
    {
      r = vfprintf(fout, fmt, ap);
      (void)fclose(fout);
    }
  va_end(ap);
  pthread_mutex_unlock(&mutex);
  return r;
}
*/
implement
tfprintf
  (pflock | fmt, arg) = let
  val (pfopt | p) = fopen_err ("/var/log/hfuselog", file_mode_aa)
  val ntot = (
//
if p > null then let
  prval Some_v (pf) = pfopt
  // [va_start (arg, fmt)] is emitted by 'atsopt'
  val ntot = vfprintf (file_mode_lte_rw_w | !p, fmt, arg)
//
  val _err = fclose1_loop (pf | p) // HX: error is ignored if there is one
//
in
  ntot
end else let
  prval None_v () = pfopt
  prval () = va_clear (arg)
in
  0 // nothing is output
end // end of [if]
//
  ) : int // end of [val]
  val () = va_end (arg)
in
  ntot // the number of bytes in the output
end // end of [tfprintf]

(* ****** ****** *)

/*
static void dologtime(void)
{
  memset((void *)&ts, 0, sizeof(ts));
  if ( clock_gettime(CLOCK_THREAD_CPUTIME_ID, &ts) >= 0 )
    tfprintf("TIME: %d %ld\n", ts.tv_sec, ts.tv_nsec);
}
*/

(* ****** ****** *)

/*
static int parts(const char *path, char **bname, char **rname)
{
  const char *sla;
  const char *p;
  int   leen;

  if ( path == NULL || path[0] == 0 || bname == NULL || rname == NULL )
    return -EINVAL;
  *bname = NULL;
  *rname = NULL;
  if ( strcmp(path, "/") == 0 )
    return 0;
  p = path+1;
  sla = strchr(p, '/');
  if ( sla == NULL )
    {
      *bname = strdup(p);
      return 0;
    }
  leen = (int)(sla - p);
  *bname = (char *)calloc(leen+1, sizeof(char));
  if ( *bname != NULL )
    memcpy(*bname, p, leen);
  *rname = strdup(sla+1);
  return 0;
}
*/
implement
parts {n} (
  path, n, bname, rname
) = let
  // nothing
in
  case+ 0 of
  | _ when n >= 2 => let
      val path1 = __tail (path) where {
        extern fun __tail
          (x: string n):<> string (n-1) = "atspre_psucc"
      } // end of [val]
      val n1 = n - 1
      val n2 = string_index_of_char_from_left (path1, '/')
    in
      if n2 >= 0 then let
        val n2 = size1_of_ssize1 (n2)
        val sbuf = string_make_substring (path1, 0, n2)
        val () = bname := strptr_of_strbuf (sbuf)
        val sbuf = string_make_substring (path1, n2+1, n1-n2-1)
        val () = rname := strptr_of_strbuf (sbuf)
      in
        // nothing
      end else let (* not found *)
        val sbuf = string_make_substring (path1, 0, n1)
        val () = bname := strptr_of_strbuf (sbuf)
        val () = rname := strptr_null (null)
      in
        // nothing
      end // end of [if]
    end // end of [_ when ...]
  | _ (*n = 1*) => let
      val () = bname := strptr_null (null)
      val () = rname := strptr_null (null)
    in
      // nothing
    end // end of [_]
end // end of [parts]

(* ****** ****** *)

/*
static
int hfuse_open (
  const char *path
, struct fuse_file_info *fi
) {
  tfprintf("open(%s, 0x%x)\n", path, fi->flags);
  dologtime();
  tfprintf("open success\n");
  dologtime();
  return 0;
}
*/
implement
hfuse_open
  (path, fi) = 0 where {
//
  val (pflock | ()) = hfuselog_lock ()
  val _err = tfprintf (pflock | "open(%s, 0x%x)\n", @(path, fi.flags))
  val _err = dologtime (pflock | (*none*))
  val () = hfuselog_unlock (pflock | (*none*))
//
  val (pflock | ()) = hfuselog_lock ()
  val _err = tfprintf(pflock | "open success\n", @())
  val _err = dologtime (pflock | (*none*))
  val () = hfuselog_unlock (pflock | (*none*))
//
} // end of [hfuse_open]

(* ****** ****** *)

/*
static int hfuse_read(const char *path, char *buf, size_t size, off_t offset,
		      struct fuse_file_info *fi)
{
  char  *b = NULL;
  char  *rest = NULL;
  size_t len;
  int    res;

  UNREF(fi);
  tfprintf("read(%s, 0x%x, %d, %d)\n", path, buf, size, offset);
  dologtime();
  res = parts(path, &b, &rest);
  if ( res < 0 )
    return res;
  res = (*f_sizep)(b, rest);
  if ( res < 0 )
    {
      if ( b != NULL )
	free((void *)b);
      if ( rest != NULL )
	free((void *)rest);
      return res;
    }
  len = (size_t)res;
  res = 0;
  if ( offset < len )
    {
      if ( (offset + size) > len)
	size = len - offset;
      res = (*f_readp)(b, rest, buf, offset, size);
    }
  else {} // do nothing
  if ( b != NULL )
    free((void *)b);
  if ( rest != NULL )
    free((void *)rest);
  tfprintf("read success\n");
  dologtime();
  return res;
}
*/

extern
fun F_SIZE {l1,l2:addr} (b: !strptr l1, r: !strptr l2): int
extern
fun F_READ {n:nat} {l:addr} (
  pfbuf: !bytes(n) @ l
| b: !strptr0, rest: !strptr0, pbuf: ptr l, ofs: off_t, len: size_t
) : int
implement
hfuse_read (
  pfbuf | path, pbuf, size, ofs, fi
) = let
  var res: int = 0
//
  val (pflock | ()) = hfuselog_lock ()
  val _err = tfprintf
    (pflock | "read(%s, 0x%p, %ld, %ld)\n", @(path, pbuf, _size, _ofs)) where {
    val _ofs = lint_of_off (ofs)
    val _size = lint_of_size (size)
  } // end of [val]
  val _err = dologtime (pflock | (*none*))
  val () = hfuselog_unlock (pflock | (*none*))
//
  val [n:int] path = string1_of_string (path)
//
  val () =
//
while (true) let
  val n = string1_length (path)
  val () = if (n = 0) then (res := (int_of_errno)EINVAL; break)
  val () = assert (n > 0)
  var b: strptr0 and rest: strptr0
  val () = parts (path, n, b, rest)
  val () =
//
while (true) let
  val () = res := F_SIZE (b, rest)
  val () = if (res < 0) then break
  val () = res := F_READ (pfbuf | b, rest, pbuf, ofs, size)
  val () = if (res < 0) then break
in
  break
end // end of [while]
//
  val () = strptr_free (b) and () = strptr_free (rest)
in
  break
end // end of [while]
//
in
  ssize_of_int(~1)
end // end of [hfuse_read]

(* ****** ****** *)

implement
hfuse_release
  (path, fi) = 0 where {
//
  val (pflock | ()) = hfuselog_lock ()
  val _err = tfprintf (pflock | "release(%s)\n", @(path))
  val _err = dologtime (pflock | (*none*))
  val () = hfuselog_unlock (pflock | (*none*))
//
  val (pflock | ()) = hfuselog_lock ()
  val _err = tfprintf(pflock | "release success\n", @())
  val _err = dologtime (pflock | (*none*))
  val () = hfuselog_unlock (pflock | (*none*))
//
} // end of [hfuse_release]

(* ****** ****** *)

(* end of [hfuse.dats] *)
