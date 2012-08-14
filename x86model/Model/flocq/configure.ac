AC_INIT([Flocq], [2.1.0],
        [Sylvie Boldo <sylvie.boldo@inria.fr>, Guillaume Melquiond <guillaume.melquiond@inria.fr>],
        [flocq])
AM_INIT_AUTOMAKE

m4_divert_push(99)
if test "$ac_init_help" = "long"; then
  ac_init_help=short
fi
m4_divert_pop(99)

m4_divert_push([HELP_ENABLE])
Fine tuning of the installation directory:
AS_HELP_STRING([--libdir=DIR], [library @<:@DIR=`$COQC -where`/user-contrib/Flocq@:>@])
m4_divert_pop([HELP_ENABLE])

AC_ARG_VAR(COQC, [Coq compiler command [coqc]])
AC_CHECK_TOOL(COQC, coqc)

AC_ARG_VAR(COQDEP, [Coq dependency analyzer command [coqdep]])
AC_CHECK_TOOL(COQDEP, coqdep)

AC_ARG_VAR(COQDOC, [Coq documentation tool [coqdoc]])
AC_CHECK_TOOL(COQDOC, coqdoc)

if test "$libdir" = '${exec_prefix}/lib'; then
  libdir='`$(COQC) -where`/user-contrib/Flocq'
fi

AC_SUBST(COQRFLAG, ['-R . Flocq'])
AC_ARG_ENABLE([prefix], AS_HELP_STRING([--disable-prefix], [do not compile files into a Flocq module]),
  [if test "$enable_prefix" = "no"; then COQRFLAG= ; fi], [])

AC_CONFIG_FILES([Makefile src/Makefile src/Flocq_version.v])
AC_OUTPUT
