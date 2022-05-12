#define PERL_NO_GET_CONTEXT
#include "EXTERN.h"
#include "perl.h"
#include "XSUB.h"

#include "ppport.h"

#include "const-c.inc"

SV * create_op_chain(pTHX_ OP * start_op, CV * cv){
    HV * op_collection_HV = newHV();
    sv_2mortal((SV*) op_collection_HV);

    char key_buffer[sizeof(OP*)+1] __attribute__ ((aligned (sizeof(OP*))));
    key_buffer[sizeof(OP*)] = 0;

    int pending_op_capacity = 100;
    int pending_op_p = 0;
    OP ** pending_ops;
    Newx(pending_ops, pending_op_capacity, OP*);
    SV ** pending_parent_cntrs;
    Newx(pending_parent_cntrs, pending_op_capacity, SV*);

    inline void enlarge_pending_ops(){
        pending_op_capacity *= 2;
        Renew(pending_ops, pending_op_capacity, OP*);
        Renew(pending_parent_cntrs, pending_op_capacity, SV*);
    }

    SV * start_entry_SV = newSV(0);
    pending_parent_cntrs[pending_op_p] = start_entry_SV;
    pending_ops[pending_op_p++] = start_op;

    while( pending_op_p ){
        OP *o = pending_ops[--pending_op_p];
        *(OP**)key_buffer = o;
        SV * op_collection_entry_SV = *hv_fetch(op_collection_HV, key_buffer, sizeof(OP*), 1);
        if( SvOK(op_collection_entry_SV) ){
            SvSetSV(pending_parent_cntrs[pending_op_p], op_collection_entry_SV);
            continue;
        }

        HV *op_bag_HV = newHV();
        SvUPGRADE(op_collection_entry_SV, SVt_RV);
        SvROK_on(op_collection_entry_SV);
        SvRV_set(op_collection_entry_SV, (SV*) op_bag_HV);
        SvSetSV(pending_parent_cntrs[pending_op_p], op_collection_entry_SV);

        hv_store(op_bag_HV, "name", 4, newSVpv(OP_NAME(o), 0), 0);
        hv_store(op_bag_HV, "desc", 4, newSVpv(OP_DESC(o), 0), 0);

        if( OP_TYPE_IS_NN(o, OP_NEXTSTATE) ||
            OP_TYPE_IS_NN(o, OP_PUSHMARK) ||
            OP_TYPE_IS_NN(o, OP_ENTERLOOP) ||
            OP_TYPE_IS_NN(o, OP_LEAVELOOP) ||
            OP_TYPE_IS_NN(o, OP_ENTER) ||
            OP_TYPE_IS_NN(o, OP_LEAVE) ||
            0
        ){
            hv_store(op_bag_HV, "~next", 5, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = o->op_next;//LINKLIST(o);
        }

        else if( OP_TYPE_IS_NN(o, OP_AASSIGN) ){
            hv_store(op_bag_HV, "~next", 5, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = o->op_next;//LINKLIST(o);
        }

        else if( OP_TYPE_IS_NN(o, OP_SASSIGN) ){
            if(o->op_private & OPpASSIGN_BACKWARDS) /* {or,and,dor}assign */
                hv_store(op_bag_HV, "flip_args", 9, newSViv(1), 0);
            if(UNLIKELY(o->op_private & OPpASSIGN_CV_TO_GV))
                hv_store(op_bag_HV, "set_module_sub", 14, newSViv(1), 0);

            hv_store(op_bag_HV, "~next", 5, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = o->op_next;//LINKLIST(o);
        }

        else if( OP_TYPE_IS_NN(o, OP_PADRANGE) ){
            PADOFFSET base = o->op_targ;
            int count = (int)(o->op_private) & OPpPADRANGE_COUNTMASK;
            hv_store(op_bag_HV, "base", 4, newSViv(base), 0);
            hv_store(op_bag_HV, "count", 5, newSViv(count), 0);
            if(o->op_flags & OPf_SPECIAL)
                hv_store(op_bag_HV, "special", 7, newSVpvn("@_", 2), 0);
            if(o->op_private & OPpLVAL_INTRO)
                hv_store(op_bag_HV, "my", 2, newSViv(1), 0);
            if((o->op_flags & OPf_WANT) == OPf_WANT_VOID)
                hv_store(op_bag_HV, "void_context", 12, newSViv(1), 0);

            PADLIST * const padlist = CvPADLIST(cv);
            PADNAMELIST * comppad = PadlistNAMES(padlist);
            SV * var_SVs[count];
            for(int i=0; i<count; ++i){
                PADNAME * name_SV = padnamelist_fetch(comppad, base+i);
                var_SVs[i] = sv_2mortal(name_SV ?
                    newSVpvf("%" PNf, PNfARG(name_SV)) :
                    newSVpvf("[%" UVuf "]", (UV)(base+i))
                );
            }
            hv_store(op_bag_HV, "var", 3, newRV_noinc((SV*) av_make(count, var_SVs)), 0);

            hv_store(op_bag_HV, "~next", 5, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = o->op_next;//LINKLIST(o);
        }

        else if(
            OP_TYPE_IS_NN(o, OP_PADSV) ||
            OP_TYPE_IS_NN(o, OP_PADAV) ||
            0
        ){
            int base = o->op_targ;
            hv_store(op_bag_HV, "base", 4, newSViv(base), 0);
            PADLIST * const padlist = CvPADLIST(cv);
            PADNAMELIST * comppad = PadlistNAMES(padlist);
            PADNAME * name_SV = padnamelist_fetch(comppad, base);
            hv_store(op_bag_HV, "var", 3, name_SV ?
                newSVpvf("%" PNf, PNfARG(name_SV)) :
                newSVpvf("[%" UVuf "]", (UV)base)
            , 0);

            hv_store(op_bag_HV, "~next", 5, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = o->op_next;//LINKLIST(o);
        }

        else if( OP_TYPE_IS_NN(o, OP_GVSV) ){
            if(UNLIKELY(o->op_private & OPpLVAL_INTRO))
                hv_store(op_bag_HV, "lval", 4, newSViv(1), 0);
            GV * gv = cGVOPo_gv;
            if( isGV_with_GP(gv) ){
                SV * name_SV = newSVpvs_flags("", SVs_TEMP);
                gv_fullname3(name_SV, gv, NULL);
                hv_store(op_bag_HV, "var", 3, name_SV, 0);
            }
            hv_store(op_bag_HV, "~next", 5, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = o->op_next;//LINKLIST(o);
        }

        else if( OP_TYPE_IS_NN(o, OP_GV) ){
            GV * gv = cGVOPo_gv;
            if( isGV_with_GP(gv) ){
                SV * name_SV = newSVpvs_flags("", SVs_TEMP);
                gv_fullname3(name_SV, gv, NULL);
                hv_store(op_bag_HV, "var", 3, name_SV, 0);
            }
            hv_store(op_bag_HV, "~next", 5, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = o->op_next;//LINKLIST(o);
        }

        else if( OP_TYPE_IS_NN(o, OP_RV2AV) ){
            const bool is_pp_rv2av = o->op_type == OP_RV2AV || o->op_type == OP_LVAVREF;
            hv_store(op_bag_HV, "type", 4, newSVpv(is_pp_rv2av ? "array" : "hash", 0), 0);

            hv_store(op_bag_HV, "~next", 5, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = o->op_next;//LINKLIST(o);
        }

        else if(
            OP_TYPE_IS_NN(o, OP_AND) ||
            OP_TYPE_IS_NN(o, OP_COND_EXPR) ||
            0
        ){
            hv_store(op_bag_HV, "~next_true", 10, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = cLOGOPo->op_other;

            if( pending_op_p==pending_op_capacity )
                enlarge_pending_ops();

            hv_store(op_bag_HV, "~next_false", 11, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = o->op_next;//LINKLIST(o);
        }

        else if(
            OP_TYPE_IS_NN(o, OP_OR) ||
            OP_TYPE_IS_NN(o, OP_DOR) ||
            OP_TYPE_IS_NN(o, OP_DORASSIGN) ||
            0
        ){
            hv_store(op_bag_HV, "~next_false", 10, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = cLOGOPo->op_other;

            if( pending_op_p==pending_op_capacity )
                enlarge_pending_ops();

            hv_store(op_bag_HV, "~next_true", 11, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = o->op_next;//LINKLIST(o);
        }

        else if( OP_TYPE_IS_NN(o, OP_UNSTACK) ){
            if(o->op_flags & OPf_SPECIAL)
                hv_store(op_bag_HV, "special", 7, newSViv(1), 0);

            hv_store(op_bag_HV, "~next", 5, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = o->op_next;//LINKLIST(o);
        }

        else if( OP_TYPE_IS_NN(o, OP_CONST) ){
            hv_store(op_bag_HV, "value", 5, SvREFCNT_inc_simple_NN(cSVOPo_sv), 0);
            hv_store(op_bag_HV, "~next", 5, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = o->op_next;//LINKLIST(o);
        }

        else if(
            OP_TYPE_IS_NN(o, OP_ADD) ||
            OP_TYPE_IS_NN(o, OP_SUBTRACT) ||
            OP_TYPE_IS_NN(o, OP_MULTIPLY) ||
            OP_TYPE_IS_NN(o, OP_DIVIDE) ||
            OP_TYPE_IS_NN(o, OP_MODULO) ||
            OP_TYPE_IS_NN(o, OP_LT) ||
            OP_TYPE_IS_NN(o, OP_GT) ||
            OP_TYPE_IS_NN(o, OP_LE) ||
            OP_TYPE_IS_NN(o, OP_GE) ||
            OP_TYPE_IS_NN(o, OP_EQ) ||
            OP_TYPE_IS_NN(o, OP_NE) ||
            OP_TYPE_IS_NN(o, OP_NCMP) ||
            OP_TYPE_IS_NN(o, OP_SLT) ||
            OP_TYPE_IS_NN(o, OP_SGT) ||
            OP_TYPE_IS_NN(o, OP_SLE) ||
            OP_TYPE_IS_NN(o, OP_SGE) ||
            OP_TYPE_IS_NN(o, OP_SEQ) ||
            OP_TYPE_IS_NN(o, OP_SNE) ||
            OP_TYPE_IS_NN(o, OP_SCMP) ||
            OP_TYPE_IS_NN(o, OP_PREINC) ||
            OP_TYPE_IS_NN(o, OP_PREDEC) ||
            OP_TYPE_IS_NN(o, OP_POSTINC) ||
            OP_TYPE_IS_NN(o, OP_POSTDEC) ||
            OP_TYPE_IS_NN(o, OP_INT) ||
            OP_TYPE_IS_NN(o, OP_ABS) ||
            OP_TYPE_IS_NN(o, OP_SQRT) ||
            OP_TYPE_IS_NN(o, OP_OCT) ||
            OP_TYPE_IS_NN(o, OP_HEX) ||
            OP_TYPE_IS_NN(o, OP_BIT_AND) ||
            OP_TYPE_IS_NN(o, OP_BIT_XOR) ||
            OP_TYPE_IS_NN(o, OP_BIT_OR) ||
            0
        ){
            hv_store(op_bag_HV, "~next", 5, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = o->op_next;//LINKLIST(o);
        }

        else if(
            OP_TYPE_IS_NN(o, OP_RAND) ||
            OP_TYPE_IS_NN(o, OP_SRAND) ||
            0
        ){
            hv_store(op_bag_HV, "maxarg", 6, newSViv(o->op_private & OPpARG4_MASK), 0);
            hv_store(op_bag_HV, "~next", 5, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = o->op_next;//LINKLIST(o);
        }

        else if(
            OP_TYPE_IS_NN(o, OP_LEAVESUB) ||
            OP_TYPE_IS_NN(o, OP_RETURN) ||
            0
        ){
        }

        else{
            hv_store(op_bag_HV, "WARN", 4, newSVpv("Unknown OP", 0), 0);
        }
    }

    Safefree(pending_parent_cntrs);
    Safefree(pending_ops);

    return start_entry_SV;
}

MODULE = Speedup		PACKAGE = Speedup		

INCLUDE: const-xs.inc

void
op_chain(SV * sub_SV)
    PPCODE:
        if( !SvROK(sub_SV) || SvTYPE(SvRV(sub_SV))!=SVt_PVCV )
            croak("pass non-coderef to op_chain()");

        CV *cv = (CV*)SvRV(sub_SV);
        OP *start_op = CvSTART(cv);

        SV *start_entry_SV = create_op_chain(aTHX_ start_op, cv);

        PUSHs(sv_2mortal(start_entry_SV));
