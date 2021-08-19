# pg_hybrid_query/Makefile

MODULE_big = pg_hybrid_query

# pg_hybrid_query
pg_hybrid_query_OBJS = pg_hybrid_query.o
OBJS += $(pg_hybrid_query_OBJS)

OBJS += $(WIN32RES)

EXTENSION = pg_hybrid_query
DATA = pg_hybrid_query--1.0.sql
PGFILEDESC = "Hybrid query extension for PostgreSQL"

REGRESS = pg_hybrid_query
PG_CPPFLAGS = -std=c++11 -Wall -g -O3 -msse4 -mpopcnt -mfma -m64 -fPIC -fpermissive 

ifdef USE_PGXS
PG_CONFIG = pg_config
PGXS := $(shell $(PG_CONFIG) --pgxs)
include $(PGXS)
else
subdir = contrib/pg_hybrid_query
top_builddir = ../..
include $(top_builddir)/src/Makefile.global
include $(top_srcdir)/contrib/contrib-global.mk
endif

wal-check: temp-install
	$(prove_check)
