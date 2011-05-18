(*
typedef long int ptrdiff_t;
typedef long unsigned int size_t;
typedef int wchar_t;

typedef signed char gint8;
typedef unsigned char guint8;
typedef signed short gint16;
typedef unsigned short guint16;
typedef signed int gint32;
typedef unsigned int guint32;
typedef signed long gint64;
typedef unsigned long guint64;
typedef signed long gssize;
typedef unsigned long gsize;
typedef gint64 goffset;
typedef signed long gintptr;
typedef unsigned long guintptr;
typedef struct _GStaticMutex GStaticMutex;
struct _GStaticMutex
{
  struct _GMutex *runtime_mutex;
  union {
    char pad[40];
    double dummy_double;
    void *dummy_pointer;
    long dummy_long;
  } static_mutex;
};
typedef union _GSystemThread GSystemThread;
union _GSystemThread
{
  char data[8];
  double dummy_double;
  void *dummy_pointer;
  long dummy_long;
};
typedef int GPid;








*)



 #define ATSCTRB_GLIB_MAJOR_VERSION 2
 #define ATSCTRB_GLIB_MINOR_VERSION 26
 #define ATSCTRB_GLIB_MICRO_VERSION 0
 #define ATSCTRB_GLIB_VERSION 1000 * (1000 * 2 + 26) + 0
