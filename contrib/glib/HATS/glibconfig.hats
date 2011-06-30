(*
typedef int ptrdiff_t;
typedef unsigned int size_t;
typedef int wchar_t;

typedef signed char gint8;
typedef unsigned char guint8;
typedef signed short gint16;
typedef unsigned short guint16;
typedef signed int gint32;
typedef unsigned int guint32;
__extension__ typedef signed long long gint64;
__extension__ typedef unsigned long long guint64;
typedef signed int gssize;
typedef unsigned int gsize;
typedef gint64 goffset;
typedef signed int gintptr;
typedef unsigned int guintptr;
typedef struct _GStaticMutex GStaticMutex;
struct _GStaticMutex
{
  struct _GMutex *runtime_mutex;
  union {
    char pad[24];
    double dummy_double;
    void *dummy_pointer;
    long dummy_long;
  } static_mutex;
};
typedef union _GSystemThread GSystemThread;
union _GSystemThread
{
  char data[4];
  double dummy_double;
  void *dummy_pointer;
  long dummy_long;
};
typedef int GPid;








*)



 #define ATSCTRB_GLIB_MAJOR_VERSION 2
 #define ATSCTRB_GLIB_MINOR_VERSION 28
 #define ATSCTRB_GLIB_MICRO_VERSION 6
 #define ATSCTRB_GLIB_VERSION 1000 * (1000 * 2 + 28) + 6
