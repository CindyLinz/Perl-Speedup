#define PERL_NO_GET_CONTEXT
#include "EXTERN.h"
#include "perl.h"
#include "XSUB.h"

#include "ppport.h"

#include "const-c.inc"

SV * create_op_chain(pTHX_ OP * start_op, CV * cv){
    if( !start_op )
        return &PL_sv_undef;

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

    inline void enlarge_pending_ops(int n){
        if( pending_op_p+n > pending_op_capacity ){
            pending_op_capacity *= 2;
            Renew(pending_ops, pending_op_capacity, OP*);
            Renew(pending_parent_cntrs, pending_op_capacity, SV*);
        }
    }

    inline SV * get_varname_sv(PADOFFSET offset){
        PADLIST * const padlist = CvPADLIST(cv);
        PADNAMELIST * comppad = PadlistNAMES(padlist);
        PADNAME * name_SV = padnamelist_fetch(comppad, offset);
        return name_SV ?
            newSVpvf("%" PNf, PNfARG(name_SV)) :
            newSVpvf("[%" UVuf "]", (UV)offset);
    }

    inline SV * get_gvname_sv(GV * gv){
        SV * name_SV = newSVpvs_flags("", 0);
        gv_fullname3(name_SV, gv, NULL);
        return name_SV;
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

        if( OP_TYPE_IS_NN(o, OP_NEXTSTATE) ){
            HV * chain_HV = Perl_refcounted_he_chain_2hv(aTHX_ ((COP*)o)->cop_hints_hash, 0);

            hv_store(op_bag_HV, "chain", 5, newRV_noinc((SV*)chain_HV), 0);
            hv_store(op_bag_HV, "~next", 5, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = o->op_next;//LINKLIST(o);
        }

        else if( OP_TYPE_IS_NN(o, OP_PUSHMARK) ||
            OP_TYPE_IS_NN(o, OP_LEAVELOOP) ||
            OP_TYPE_IS_NN(o, OP_ENTER) ||
            OP_TYPE_IS_NN(o, OP_LEAVE) ||
            OP_TYPE_IS_NN(o, OP_ARGCHECK) ||
            0
        ){
            hv_store(op_bag_HV, "~next", 5, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = o->op_next;//LINKLIST(o);
        }

        else if( OP_TYPE_IS_NN(o, OP_ENTERLOOP)){
            enlarge_pending_ops(6);

            if( cLOOPo->op_first ){
                hv_store(op_bag_HV, "~first", 6, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
                pending_ops[pending_op_p++] = cLOOPo->op_first;
            }
            if( cLOOPo->op_last ){
                hv_store(op_bag_HV, "~last", 5, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
                pending_ops[pending_op_p++] = cLOOPo->op_last;
            }
            if( cLOOPo->op_redoop ){
                hv_store(op_bag_HV, "~redoop", 7, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
                pending_ops[pending_op_p++] = cLOOPo->op_redoop;
            }
            if( cLOOPo->op_nextop ){
                hv_store(op_bag_HV, "~nextop", 7, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
                pending_ops[pending_op_p++] = cLOOPo->op_nextop;
            }
            if( cLOOPo->op_lastop ){
                hv_store(op_bag_HV, "~lastop", 7, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
                pending_ops[pending_op_p++] = cLOOPo->op_lastop;
            }

            hv_store(op_bag_HV, "~next", 5, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = o->op_next;//LINKLIST(o);
        }

        else if( OP_TYPE_IS_NN(o, OP_AASSIGN) ){
            hv_store(op_bag_HV, "~next", 5, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = o->op_next;//LINKLIST(o);
        }

        else if( OP_TYPE_IS_NN(o, OP_SASSIGN) ){
            hv_store(op_bag_HV, "flip_args", 9, newSViv(o->op_private & OPpASSIGN_BACKWARDS), 0); /* {or,and,dor}assign */
            hv_store(op_bag_HV, "set_module_sub", 14, newSViv(o->op_private & OPpASSIGN_CV_TO_GV), 0);

            hv_store(op_bag_HV, "~next", 5, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = o->op_next;//LINKLIST(o);
        }

        else if( OP_TYPE_IS_NN(o, OP_PADRANGE) ){
            PADOFFSET base = o->op_targ;
            int count = (int)(o->op_private) & OPpPADRANGE_COUNTMASK;
            hv_store(op_bag_HV, "offset", 6, newSViv(base), 0);
            hv_store(op_bag_HV, "count", 5, newSViv(count), 0);
            hv_store(op_bag_HV, "special", 7, newSViv(o->op_flags & OPf_SPECIAL), 0);
            hv_store(op_bag_HV, "my", 2, newSViv(o->op_private & OPpLVAL_INTRO), 0);
            hv_store(op_bag_HV, "void_context", 12, newSViv((o->op_flags & OPf_WANT) == OPf_WANT_VOID), 0);

            PADLIST * const padlist = CvPADLIST(cv);
            PADNAMELIST * comppad = PadlistNAMES(padlist);
            SV * var_SVs[count];
            for(int i=0; i<count; ++i)
                var_SVs[i] = sv_2mortal(get_varname_sv(base+i));
            hv_store(op_bag_HV, "var", 3, newRV_noinc((SV*) av_make(count, var_SVs)), 0);

            hv_store(op_bag_HV, "~next", 5, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = o->op_next;//LINKLIST(o);
        }

        else if( OP_TYPE_IS_NN(o, OP_PADSV) ){
            PADOFFSET base = o->op_targ;
            hv_store(op_bag_HV, "offset", 6, newSViv(base), 0);
            hv_store(op_bag_HV, "var", 3, get_varname_sv(base), 0);
            hv_store(op_bag_HV, "state", 5, newSViv(o->op_flags & OPf_MOD ? o->op_private & OPpPAD_STATE : 0), 0);
            hv_store(op_bag_HV, "my", 2, newSViv(o->op_flags & OPf_MOD && !(o->op_private & OPpPAD_STATE) ? o->op_private & OPpLVAL_INTRO : 0), 0);
            hv_store(op_bag_HV, "vivify", 6, newSViv(o->op_flags & OPf_MOD ? o->op_private & OPpDEREF: 0), 0);
            hv_store(op_bag_HV, "~next", 5, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = o->op_next;//LINKLIST(o);
        }
        else if( OP_TYPE_IS_NN(o, OP_PADAV) ){
            PADOFFSET base = o->op_targ;
            if( o->op_private & OPpLVAL_INTRO ){
                if( o->op_private & OPpPAD_STATE )
                    hv_store(op_bag_HV, "state", 5, newSViv(o->op_private & OPpPAD_STATE), 0);
                else
                    hv_store(op_bag_HV, "my", 2, newSViv(o->op_private & OPpLVAL_INTRO), 0);
            }
            hv_store(op_bag_HV, "maybe_lvsub", 11, newSViv(o->op_private & OPpMAYBE_LVSUB), 0);
            hv_store(op_bag_HV, "ref", 3, newSViv(o->op_flags & OPf_REF), 0);
            hv_store(op_bag_HV, "offset", 6, newSViv(base), 0);
            hv_store(op_bag_HV, "var", 3, get_varname_sv(base), 0);
            hv_store(op_bag_HV, "~next", 5, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = o->op_next;//LINKLIST(o);
        }

        else if( OP_TYPE_IS_NN(o, OP_GVSV) ){
            hv_store(op_bag_HV, "lval", 4, newSViv(o->op_private & OPpLVAL_INTRO), 0);
            GV * gv = cGVOPo_gv;
            if( isGV_with_GP(gv) )
                hv_store(op_bag_HV, "var", 3, get_gvname_sv(gv), 0);
            hv_store(op_bag_HV, "~next", 5, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = o->op_next;//LINKLIST(o);
        }

        else if( OP_TYPE_IS_NN(o, OP_GV) ){
            GV * gv = cGVOPo_gv;
            if( isGV_with_GP(gv) )
                hv_store(op_bag_HV, "var", 3, get_gvname_sv(gv), 0);
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
            enlarge_pending_ops(2);

            hv_store(op_bag_HV, "~true", 5, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = cLOGOPo->op_other;

            hv_store(op_bag_HV, "~false", 6, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = o->op_next;//LINKLIST(o);
        }

        else if(
            OP_TYPE_IS_NN(o, OP_OR) ||
            OP_TYPE_IS_NN(o, OP_DOR) ||
            OP_TYPE_IS_NN(o, OP_DORASSIGN) ||
            0
        ){
            enlarge_pending_ops(2);

            hv_store(op_bag_HV, "~false", 6, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = cLOGOPo->op_other;

            hv_store(op_bag_HV, "~true", 5, pending_parent_cntrs[pending_op_p] =newSV(0), 0);
            pending_ops[pending_op_p++] = o->op_next;//LINKLIST(o);
        }

        else if( OP_TYPE_IS_NN(o, OP_UNSTACK) ){
            hv_store(op_bag_HV, "special", 7, newSViv(o->op_flags & OPf_SPECIAL), 0);

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
            OP_TYPE_IS_NN(o, OP_NBIT_AND) ||
            OP_TYPE_IS_NN(o, OP_NBIT_XOR) ||
            OP_TYPE_IS_NN(o, OP_NBIT_OR) ||
            OP_TYPE_IS_NN(o, OP_SBIT_AND) ||
            OP_TYPE_IS_NN(o, OP_SBIT_XOR) ||
            OP_TYPE_IS_NN(o, OP_SBIT_OR) ||
            0
        ){
            hv_store(op_bag_HV, "target_at", 9, newSVpv(o->op_flags & OPf_STACKED ? "stack" : "op_targ", 0), 0);
            if( !(o->op_flags & OPf_STACKED) ){
                hv_store(op_bag_HV, "op_targ", 7, newSViv(o->op_targ), 0);
                hv_store(op_bag_HV, "op_targ_var", 11, get_varname_sv(o->op_targ), 0);
            }
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

        else if( OP_TYPE_IS_NN(o, OP_LAST) ){
            IV special = o->op_flags & OPf_SPECIAL;
            hv_store(op_bag_HV, "special", 7, newSViv(special), 0);
            if( !special ){
                IV stacked = o->op_flags & OPf_STACKED;
                hv_store(op_bag_HV, "stacked", 7, newSViv(stacked), 0);
                if( !stacked )
                    hv_store(op_bag_HV, "target_label", 12, newSVpv(cPVOPo->op_pv, 0), 0);
            }
        }

        else if( OP_TYPE_IS_NN(o, OP_MULTIDEREF) ){
            hv_store(op_bag_HV, "exists", 6, newSViv(o->op_private & OPpMULTIDEREF_EXISTS), 0);
            hv_store(op_bag_HV, "delete", 6, newSViv(o->op_private & OPpMULTIDEREF_DELETE), 0);
            hv_store(op_bag_HV, "lval", 4, newSViv(o->op_flags & OPf_MOD), 0); // XXX ignore lvalue sub LVRET
            hv_store(op_bag_HV, "defer", 5, newSViv(o->op_private & OPpLVAL_DEFER), 0);
            hv_store(op_bag_HV, "localizing", 10, newSViv(o->op_private & OPpLVAL_INTRO), 0);

            AV * accessor_AV = newAV();
            hv_store(op_bag_HV, "accessor", 8, newRV_noinc((SV*) accessor_AV), 0);
            HV * accessor_elem_HV;

            UNOP_AUX_item *items = cUNOP_AUXo->op_aux;
            UV actions = items->uv;
            while(1){
                switch (actions & MDEREF_ACTION_MASK) {
                    case MDEREF_reload:
                        actions = (++items)->uv;
                        continue;
                    case MDEREF_AV_padav_aelem:                 /* $lex[...] */
                        ++items;
                        accessor_elem_HV = newHV();
                        av_push(accessor_AV, newRV_noinc((SV*)accessor_elem_HV));
                        hv_store(accessor_elem_HV, "type", 4, newSVpv("lex_array", 0), 0);
                        hv_store(accessor_elem_HV, "offset", 6, newSViv(items->pad_offset), 0);
                        hv_store(accessor_elem_HV, "var", 3, get_varname_sv(items->pad_offset), 0);
                        goto do_AV_aelem;
                    case MDEREF_AV_gvav_aelem:                  /* $pkg[...] */
                        ++items;
                        accessor_elem_HV = newHV();
                        av_push(accessor_AV, newRV_noinc((SV*)accessor_elem_HV));
                        hv_store(accessor_elem_HV, "type", 4, newSVpv("pkg_array", 0), 0);
                        {
                            GV * gv = (GV*)UNOP_AUX_item_sv(items)
                            hv_store(accessor_elem_HV, "var", 3, get_gvname_sv(gv), 0);
                        }
                        goto do_AV_aelem;
                    case MDEREF_AV_pop_rv2av_aelem:             /* expr->[...] */
                        accessor_elem_HV = newHV();
                        av_push(accessor_AV, newRV_noinc((SV*)accessor_elem_HV));
                        hv_store(accessor_elem_HV, "type", 4, newSVpv("expr_array", 0), 0);
                        goto do_AV_aelem;
                    case MDEREF_AV_gvsv_vivify_rv2av_aelem:     /* $pkg->[...] */
                        ++items;
                        accessor_elem_HV = newHV();
                        av_push(accessor_AV, newRV_noinc((SV*)accessor_elem_HV));
                        hv_store(accessor_elem_HV, "type", 4, newSVpv("pkg_arrayref", 0), 0);
                        {
                            GV * gv = (GV*)UNOP_AUX_item_sv(items);
                            hv_store(accessor_elem_HV, "var", 3, get_gvname_sv(gv), 0);
                        }
                        goto do_AV_aelem;
                    case MDEREF_AV_padsv_vivify_rv2av_aelem:     /* $lex->[...] */
                        ++items;
                        accessor_elem_HV = newHV();
                        av_push(accessor_AV, newRV_noinc((SV*)accessor_elem_HV));
                        hv_store(accessor_elem_HV, "type", 4, newSVpv("lex_arrayref", 0), 0);
                        hv_store(accessor_elem_HV, "offset", 6, newSViv(items->pad_offset), 0);
                        hv_store(accessor_elem_HV, "var", 3, get_varname_sv(items->pad_offset), 0);
                        goto do_AV_aelem;
                    case MDEREF_AV_vivify_rv2av_aelem:           /* vivify, ->[...] */
                        accessor_elem_HV = newHV();
                        av_push(accessor_AV, newRV_noinc((SV*)accessor_elem_HV));
                        hv_store(accessor_elem_HV, "type", 4, newSVpv("vivify_arrayref", 0), 0);
                        goto do_AV_aelem;
                    do_AV_aelem:
                        switch (actions & MDEREF_INDEX_MASK) {
                            case MDEREF_INDEX_none:
                                goto finish;
                            case MDEREF_INDEX_const:
                                hv_store(accessor_elem_HV, "index", 5, newSViv((++items)->iv), 0);
                                break;
                            case MDEREF_INDEX_padsv:
                                ++items;
                                hv_store(accessor_elem_HV, "index_offset", 12, newSViv(items->pad_offset), 0);
                                hv_store(accessor_elem_HV, "index_var", 9, get_varname_sv(items->pad_offset), 0);
                                break;
                            case MDEREF_INDEX_gvsv:
                                ++items;
                                {
                                    GV * gv = (GV*) UNOP_AUX_item_sv(items);
                                    hv_store(accessor_elem_HV, "index_pkgvar", 12, get_gvname_sv(gv), 0);
                                }
                                break;
                        }
                        if(!(actions & MDEREF_FLAG_last))
                            break;
                        goto finish;
                    case MDEREF_HV_padhv_helem:                 /* $lex{...} */
                        ++items;
                        accessor_elem_HV = newHV();
                        av_push(accessor_AV, newRV_noinc((SV*)accessor_elem_HV));
                        hv_store(accessor_elem_HV, "type", 4, newSVpv("lex_hash", 0), 0);
                        hv_store(accessor_elem_HV, "offset", 6, newSViv(items->pad_offset), 0);
                        hv_store(accessor_elem_HV, "var", 3, get_varname_sv(items->pad_offset), 0);
                        goto do_HV_helem;
                    case MDEREF_HV_gvhv_helem:                  /* $pkg{...} */
                        ++items;
                        accessor_elem_HV = newHV();
                        av_push(accessor_AV, newRV_noinc((SV*)accessor_elem_HV));
                        hv_store(accessor_elem_HV, "type", 4, newSVpv("pkg_hash", 0), 0);
                        {
                            GV * gv = (GV*)UNOP_AUX_item_sv(items)
                            hv_store(accessor_elem_HV, "var", 3, get_gvname_sv(gv), 0);
                        }
                        goto do_HV_helem;
                    case MDEREF_HV_pop_rv2hv_helem:             /* expr->{...} */
                        accessor_elem_HV = newHV();
                        av_push(accessor_AV, newRV_noinc((SV*)accessor_elem_HV));
                        hv_store(accessor_elem_HV, "type", 4, newSVpv("expr_hash", 0), 0);
                        goto do_HV_helem;
                    case MDEREF_HV_gvsv_vivify_rv2hv_helem:     /* $pkg->{...} */
                        ++items;
                        accessor_elem_HV = newHV();
                        av_push(accessor_AV, newRV_noinc((SV*)accessor_elem_HV));
                        hv_store(accessor_elem_HV, "type", 4, newSVpv("pkg_hashref", 0), 0);
                        {
                            GV * gv = (GV*)UNOP_AUX_item_sv(items)
                            hv_store(accessor_elem_HV, "var", 3, get_gvname_sv(gv), 0);
                        }
                        goto do_HV_helem;
                    case MDEREF_HV_padsv_vivify_rv2hv_helem:    /* $lex->{...} */
                        ++items;
                        accessor_elem_HV = newHV();
                        av_push(accessor_AV, newRV_noinc((SV*)accessor_elem_HV));
                        hv_store(accessor_elem_HV, "type", 4, newSVpv("lex_hashref", 0), 0);
                        hv_store(accessor_elem_HV, "offset", 6, newSViv(items->pad_offset), 0);
                        hv_store(accessor_elem_HV, "var", 3, get_varname_sv(items->pad_offset), 0);
                        goto do_HV_helem;
                    case MDEREF_HV_vivify_rv2hv_helem:
                        accessor_elem_HV = newHV();
                        av_push(accessor_AV, newRV_noinc((SV*)accessor_elem_HV));
                        hv_store(accessor_elem_HV, "type", 4, newSVpv("vivify_hashref", 0), 0);
                        goto do_HV_helem;
                    do_HV_helem:
                        switch (actions & MDEREF_INDEX_MASK) {
                            case MDEREF_INDEX_none:
                                goto finish;

                            case MDEREF_INDEX_const:
                                {
                                    SV * sv = UNOP_AUX_item_sv(++items);
                                    hv_store(accessor_elem_HV, "key", 3, newSVsv(sv), 0);
                                }
                                break;

                            case MDEREF_INDEX_padsv:
                                ++items;
                                hv_store(accessor_elem_HV, "key_offset", 10, newSViv(items->pad_offset), 0);
                                hv_store(accessor_elem_HV, "key_var", 7, get_varname_sv(items->pad_offset), 0);
                                break;

                            case MDEREF_INDEX_gvsv:
                                ++items;
                                {
                                    GV * gv = (GV*) UNOP_AUX_item_sv(items);
                                    hv_store(accessor_elem_HV, "key_pkgvar", 10, get_gvname_sv(gv), 0);
                                }
                                break;
                        }
                        if(!(actions & MDEREF_FLAG_last))
                            break;
                        goto finish;
                }
                actions >>= MDEREF_SHIFT;
            }
            finish:;

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
