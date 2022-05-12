#define PERL_NO_GET_CONTEXT
#include "EXTERN.h"
#include "perl.h"
#include "XSUB.h"

#include "ppport.h"

#include "const-c.inc"

MODULE = Speedup		PACKAGE = Speedup		

INCLUDE: const-xs.inc

void
op_chain(SV * sub_SV)
    PPCODE:
        if( !SvROK(sub_SV) || SvTYPE(SvRV(sub_SV))!=SVt_PVCV )
            croak("pass non-coderef to op_chain()");

        CV *cv = (CV*)SvRV(sub_SV);
        OP *start_op = CvSTART(cv);

        PUSHs(&PL_sv_undef);
