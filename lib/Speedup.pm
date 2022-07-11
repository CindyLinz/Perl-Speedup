package Speedup;

use 5.030002;
use strict;
use warnings;
use Carp;

require Exporter;
use AutoLoader;

our @ISA = qw(Exporter);

our %EXPORT_TAGS = ( 'all' => [ qw(
	
) ] );

our @EXPORT_OK = ( @{ $EXPORT_TAGS{'all'} } );

our @EXPORT = qw(
	
);

our $VERSION = '0.01';

require XSLoader;
XSLoader::load('Speedup', $VERSION);

use List::Util qw(uniqstr);

sub destroy_op_chain {
    my @stack = @_;
    while(my $op = pop @stack) {
        for my $key (keys %$op) {
            if( substr($key, 0, 1) eq '~' ) {
                push @stack, delete $op->{$key};
            }
        }
    }
}

sub gen_code {
    my($thing, $op_chain) = @_;

    my @stack = ([[]]);
    my @op_stack;
    my $uid = 0;
    my $label_uid = 0;
    my $abort = 0;
    my @XS;
    my %var; # key: padX, tX,
             # value: {input/output}[union][intersection]

    my %IMP =
      ( ANY =>
        { accept => [qw(ANY REF STR NUM INT BOOL DEF NONE)]
        , decl =>
          sub {
            my($symbol, $comment) = @_;
            push @XS, "SV * $symbol = sv_2mortal(newSV(0)); // (ANY) $comment";
          }
        , const =>
          sub {
            my($symbol, $value) = @_;
            if( defined $value ) {
                my $len = length $value;
                my $str = $value =~ s/[^\x20-\x7e]/sprintf('\x%02X',ord($&))/ger;
                push @XS, qq(sv_setpvn($symbol, "$str", $len););
            } else {
                push @XS, qq(SvSetSV($symbol, &PL_sv_undef););
            }
          }
        , ANY =>
          sub {
            my($from, $to) = @_;
            push @XS, "SvSetSV($to, $from);";
          }
        , DEF =>
          sub {
            my($from, $to) = @_;
            push @XS, "$to = SvOK($from);";
          }
        , BOOL =>
          sub {
            my($from, $to) = @_;
            push @XS, "$to = !!SvIV($from);";
          }
        , NUM =>
          sub {
            my($from, $to) = @_;
            push @XS, "$to = SvNV($from);";
          }
        , NUMDEF =>
          sub {
            my($from, $to) = @_;
            push @XS
                , "if( SvOK($from) )"
                , "  $to = SvNV($from);"
                , "else"
                , "  $to = -NV_MAX;"
                ;
          }
        , INT =>
          sub {
            my($from, $to) = @_;
            push @XS, "$to = SvIV($from);";
          }
        , INTDEF =>
          sub {
            my($from, $to) = @_;
            push @XS
                , "if( SvOK($from) )"
                , "  $to = SvIV($from);"
                , "else"
                , "  $to = IV_MIN;"
                ;
          }
        , NUM =>
          sub {
            my($from, $to) = @_;
            push @XS, "$to.NUM = SvNV($from);";
          }
        , NUMDEF =>
          sub {
            my($from, $to) = @_;
            push @XS
                , "if( SvOK($from) )"
                , "  $to.NUM = SvNV($from);"
                , "else"
                , "  $to.NUM = -NV_MAX;"
                ;
          }
        , INTNUM =>
          sub {
            my($from, $to) = @_;
            push @XS
                , "if( SvIV_please_nomg($from) )"
                , "  $to.INT = SvIV($from);"
                , "else{"
                , "  $to.INT = IV_MIN;"
                , "  $to.NUM = SvNV($from);"
                , "}"
                ;
          }
        , INTNUMDEF =>
          sub {
            my($from, $to) = @_;
            push @XS
                , "if( SvOK($from) ){"
                , "  if( SvIV_please_nomg($from) )"
                , "    $to.INT = SvIV($from);"
                , "  else{"
                , "    $to.INT = IV_MIN;"
                , "    $to.NUM = SvNV($from);"
                , "  }"
                , "}"
                , "else{"
                , "  $to.INT = IV_MIN;"
                , "  $to.NUM = -NV_MAX;"
                , "}"
                ;
          }
        }
      , DEF =>
        { accept => [qw(DEF NONE)]
        , decl =>
          sub {
            my($symbol, $comment) = @_;
            push @XS, "char $symbol; // (DEF) $comment";
          }
        , const =>
          sub {
            my($symbol, $value) = @_;
            $value = defined $value ? 1 : 0;
            push @XS, "$symbol = $value;";
          }
        # consumed by 'defined' directly, no convertion needed
        }
      , BOOL =>
        { accept => [qw(BOOL NONE)]
        , decl =>
          sub {
            my($symbol, $comment) = @_;
            push @XS, "char $symbol; // (BOOL) $comment";
          }
        , const =>
          sub {
            my($symbol, $value) = @_;
            $value = $value ? 1 : 0;
            push @XS, "$symbol = $value;";
          }
        , BOOL =>
          sub {
            my($from, $to) = @_;
            push @XS, "$to = $from;";
          }
        , INT => "BOOL,BOOL"
        , NUM => "BOOL,BOOL"
        , INTNUM =>
          sub {
            my($from, $to) = @_;
            push @XS, "$to.INT = $from;";
          }
        # consumed by 'and', 'or' directly, no convertion needed
        }
      , INT =>
        { accept => [qw(INT BOOL NONE)]
        , decl =>
          sub {
            my($symbol, $comment) = @_;
            push @XS, "IV $symbol; // (INT) $comment";
          }
        , const =>
          sub {
            my($symbol, $value) = @_;
            $value = int $value;
            push @XS, "$symbol = $value\LL;";
          }
        , ANY =>
          sub {
            my($from, $to) = @_;
            push @XS, "sv_setiv($to, $from);";
          }
        , DEF =>
          sub {
            my($from, $to) = @_;
            push @XS, "$to = 1;";
          }
        , BOOL =>
          sub {
            my($from, $to) = @_;
            push @XS, "$to = $from!=0;";
          }
        , INT =>
          sub {
            my($from, $to) = @_;
            push @XS, "$to = $from;";
          }
        , INTDEF => "INT,INT"
        , NUM =>
          sub {
            my($from, $to) = @_;
            push @XS, "$to = (NV) $from;";
          }
        , NUMDEF => "INT,NUM"
        , INTNUM =>
          sub {
            my($from, $to) = @_;
            push @XS, "$to.INT = $from;";
          }
        , INTNUMDEF => "INT,INTNUM"
        }
      , INTDEF => # INT|DEF
        { accept => [qw(INT BOOL DEF NONE)]
        , decl =>
          sub {
            my($symbol, $comment) = @_;
            push @XS, "IV $symbol; // (INTDEF) $comment";
          }
        , const =>
          sub {
            my($symbol, $value) = @_;
            $value = defined $value ? int($value).'LL' : 'IV_MIN';
            push @XS, "$symbol = $value;";
          }
        , ANY =>
          sub {
            my($from, $to) = @_;
            push @XS
                , "if( SvOK($from) )"
                , "  sv_setiv($to, $from);"
                , "else"
                , "  SvSetSV($to, &PL_sv_undef);"
                ;
          }
        , DEF =>
          sub {
            my($from, $to) = @_;
            push @XS, "$to = $from!=IV_MIN;";
          }
        , BOOL =>
          sub {
            my($from, $to) = @_;
            push @XS, "$to = $from!=IV_MIN && $from!=0;";
          }
        , INT =>
          sub {
            my($from, $to) = @_;
            push @XS
                , "if( $from==IV_MIN )"
                , "  $to = 0;"
                , "else"
                , "  $to = $from;"
                ;
          }
        , INTDEF => "INT,INT"
        , NUM =>
          sub {
            my($from, $to) = @_;
            push @XS
                , "if( $from==IV_MIN )"
                , "  $to = 0;"
                , "else"
                , "  $to = (NV) $from;"
                ;
          }
        , NUMDEF =>
          sub {
            my($from, $to) = @_;
            push @XS
                , "if( $from==IV_MIN )"
                , "  $to = -NV_MAX;"
                , "else"
                , "  $to = (NV) $from;";
                ;
          }
        , INTNUM =>
          sub {
            my($from, $to) = @_;
            push @XS
                , "if( $from==IV_MIN )"
                , "  $to.INT = 0;"
                , "else"
                , "  $to.INT = $from;"
                ;
          }
        , INTNUMDEF =>
          sub {
            my($from, $to) = @_;
            push @XS
                , "$to.INT = $from;"
                , "if( $from==IV_MIN )"
                , "  $to.NUM = -NV_MAX;"
                ;
          }
        }
      , NUM =>
        { accept => [qw(NUM BOOL NONE)]
        , decl =>
          sub {
            my($symbol, $comment) = @_;
            push @XS, "NV $symbol; // (NUM) $comment";
          }
        , const =>
          sub {
            my($symbol, $value) = @_;
            $value = 0+$value;
            push @XS, "$symbol = $value;";
          }
        , ANY =>
          sub {
            my($from, $to) = @_;
            push @XS, "sv_setnv($to, $from);";
          }
        , DEF => "INT,DEF"
        , BOOL =>
          sub {
            my($from, $to) = @_;
            push @XS, "$to = $from!=0 && !Perl_isnan($from);";
          }
        , INT =>
          sub {
            my($from, $to) = @_;
            push @XS, "$to = (IV)($from + .5);";
          }
        , INTDEF => "NUM,INT"
        , NUM =>
          sub {
            my($from, $to) = @_;
            push @XS, "$to = $from;";
          }
        , NUMDEF => "NUM,NUM"
        , INTNUM =>
          sub {
            my($from, $to) = @_;
            push @XS
                , "$to.INT = IV_MIN;"
                , "$to.NUM = $from;"
                ;
          }
        , INTNUMDEF => "NUM,INTNUM"
        }
      , NUMDEF => # NUM|DEF
        { accept => [qw(NUM BOOL DEF NONE)]
        , decl =>
          sub {
            my($symbol, $comment) = @_;
            push @XS, "NV $symbol; // (NUMDEF) $comment";
          }
        , const =>
          sub {
            my($symbol, $value) = @_;
            $value = defined $value ? 0+$value : '-NV_MAX';
            push @XS, "$symbol = $value;";
          }
        , ANY =>
          sub {
            my($from, $to) = @_;
            push @XS
                , "if( $from == -NV_MAX )"
                , "  SvSetSV($to, &PL_sv_undef);"
                , "else"
                , "  sv_setnv($to, $from);";
                ;
          }
        , DEF =>
          sub {
            my($from, $to) = @_;
            push @XS, "$to = $from!=-NV_MAX;";
          }
        , BOOL =>
          sub {
            my($from, $to) = @_;
            push @XS, "$to = $from!=-NV_MAX && $from!=0 && !Perl_isnan($from);";
          }
        , INT =>
          sub {
            my($from, $to) = @_;
            push @XS
                , "if( $from == -NV_MAX )"
                , "  $to = 0;"
                , "else"
                , "  $to = (IV)($from + .5);";
                ;
          }
        , INTDEF =>
          sub {
            my($from, $to) = @_;
            push @XS
                , "if( $from == -NV_MAX )"
                , "  $to = IV_MIN;"
                , "else"
                , "  $to = (IV)($from + .5);";
                ;
          }
        , NUM =>
          sub {
            my($from, $to) = @_;
            push @XS
                , "if( $from == -NV_MAX )"
                , "  $to = 0;"
                , "else"
                , "  $to = $from;";
                ;
          }
        , NUMDEF =>
          sub {
            my($from, $to) = @_;
            push @XS, "$to = $from;";
          }
        , INTNUM =>
          sub {
            my($from, $to) = @_;
            push @XS
                , "$to.INT = IV_MIN;"
                , "if( $from == -NV_MAX )"
                , "  $to.NUM = 0;"
                , "else"
                , "  $to.NUM = $from;";
                ;
          }
        , INTNUMDEF =>
          sub {
            my($from, $to) = @_;
            push @XS
                , "$to.INT = IV_MIN;"
                , "$to.NUM = $from;"
                ;
          }
        }
      , INTNUM => # INT|NUM
        { accept => [qw(NUM INT BOOL NONE)]
        , decl =>
          sub {
            my($symbol, $comment) = @_;
            push @XS, "IVNV_t $symbol; // (INTNUM) $comment";
          }
        , const =>
          sub {
            my($symbol, $value) = @_;
            if( $value == int $value ) {
                push @XS, "$symbol.INT = $value\LL;";
            } else {
                $value = 0+$value;
                push @XS
                    , "$symbol.INT = IV_MIN;"
                    , "$symbol.NUM = $value;"
                    ;
            }
          }
        , ANY =>
          sub {
            my($from, $to) = @_;
            push @XS
                , "if( $from.INT != IV_MIN )"
                , "  sv_setiv($to, $from.INT);"
                , "else"
                , "  sv_setnv($to, $from.NUM);"
                ;
          }
        , DEF => "INT,DEF"
        , BOOL =>
          sub {
            my($from, $to) = @_;
            push @XS, "$to = $from.INT!=0 && $from.NUM!=0 && !Perl_isnan($from.NUM);";
          }
        , INT =>
          sub {
            my($from, $to) = @_;
            push @XS
                , "if( $from.INT != IV_MIN )"
                , "  $to = $from.INT;"
                , "else"
                , "  $to = (IV)($from.NUM + .5);";
                ;
          }
        , INTDEF => "INTNUM,INT"
        , NUM =>
          sub {
            my($from, $to) = @_;
            push @XS
                , "if( $from.INT != IV_MIN )"
                , "  $to = (NV)$from.INT;"
                , "else"
                , "  $to = $from.NUM;";
                ;
          }
        , NUMDEF => "INTNUM,NUM"
        , INTNUM =>
          sub {
            my($from, $to) = @_;
            push @XS, "$to = $from;";
          }
        , INTNUMDEF => "INTNUM,INTNUM"
        }
      , INTNUMDEF => # INT|NUM|DEF
        { accept => [qw(NUM INT BOOL DEF NONE)]
        , decl =>
          sub {
            my($symbol, $comment) = @_;
            push @XS, "IVNV_t $symbol; // (INTNUMDEF) $comment";
          }
        , const =>
          sub {
            my($symbol, $value) = @_;
            if( defined $value ) {
                if( $value == int $value ) {
                    push @XS, "$symbol.INT = $value\LL;";
                } else {
                    $value = 0+$value;
                    push @XS
                        , "$symbol.INT = IV_MIN;"
                        , "$symbol.NUM = $value;"
                        ;
                }
            } else {
                    push @XS
                        , "$symbol.INT = IV_MIN;"
                        , "$symbol.NUM = -NV_MAX;"
                        ;
            }
          }
        , ANY =>
          sub {
            my($from, $to) = @_;
            push @XS
                , "if( $from.INT != IV_MIN )"
                , "  sv_setiv($to, $from.INT);"
                , "else if( $from.NUM != -NV_MAX )"
                , "  sv_setnv($to, $from.NUM);"
                , "else"
                , "  SvSetSV($to, &PL_sv_undef);"
                ;
          }
        , DEF =>
          sub {
            my($from, $to) = @_;
            push @XS, "$to = $from.INT!=IV_MIN || $from.NUM!=-NV_MAX;";
          }
        , BOOL =>
          sub {
            my($from, $to) = @_;
            push @XS
                , "if( $from.INT!=IV_MIN )"
                , "  $to = $from.INT!=0;"
                , "else"
                , "  $to = $from.NUM!=0 && $from.NUM!=-NV_MAX;"
                ;
          }
        , INT =>
          sub {
            my($from, $to) = @_;
            push @XS
                , "if( $from.INT!=IV_MIN )"
                , "  $to = $from.INT;"
                , "else if( $from.NUM!=-NV_MAX )"
                , "  $to = (IV)($from.NUM + .5);"
                , "else"
                , "  $to = 0;"
                ;
          }
        , INTDEF =>
          sub {
            my($from, $to) = @_;
            push @XS
                , "if( $from.INT!=IV_MIN )"
                , "  $to = $from.INT;"
                , "else if( $from.NUM!=-NV_MAX )"
                , "  $to = (IV)($from.NUM + .5);"
                , "else"
                , "  $to = IV_MIN;"
                ;
          }
        , NUM =>
          sub {
            my($from, $to) = @_;
            push @XS
                , "if( $from.INT!=IV_MIN )"
                , "  $to = (NV)$from.INT;"
                , "else if( $from.NUM!=-NV_MAX )"
                , "  $to = $from.NUM;"
                , "else"
                , "  $to = 0;"
                ;
          }
        , NUMDEF =>
          sub {
            my($from, $to) = @_;
            push @XS
                , "if( $from.INT!=IV_MIN )"
                , "  $to = (NV)$from.INT;"
                , "else"
                , "  $to = $from.NUM;"
                ;
          }
        , INTNUM =>
          sub {
            my($from, $to) = @_;
            push @XS
                , "if( $from.INT==IV_MIN && $from.NUM==-NV_MAX )"
                , "  $to.INT = 0;"
                , "else"
                , "  $to = $from;"
                ;
          }
        , INTNUMDEF =>
          sub {
            my($from, $to) = @_;
            push @XS, "$to = $from;";
          }
        }
      );
    for my $outer (values %IMP) {
        for my $inner (values %$outer) {
            if( !ref($inner) && $inner =~ /\A([^,]+),([^,]+)\z/ ) {
                $inner = $IMP{$1}{$2};
            }
        }
    }
    while(my($name, $imp) = each %IMP) {
        $imp->{name} = $name;
    }
    my $best_imp = sub {
        my @type = ref $_[0] ? @{$_[0]} : ($_[0]);
        my($need_type) = @_;
        my($best_imp, $best_imp_score) = ('ANY', 0+@{$IMP{ANY}{accept}});
        for my $imp (values %IMP) {
            next if( @{$imp->{accept}} >= $best_imp_score );
            my $accepted = 1;
            for my $type (@type) {
                my $found = 0;
                for my $t (values @{$imp->{accept}}) {
                    if( $t eq $type ) {
                        $found = 1;
                        last;
                    }
                }
                if( !$found ) {
                    $accepted = 0;
                    last;
                }
            }
            if( $accepted ) {
                $best_imp = $imp->{name};
                $best_imp_score = @{$imp->{accept}};
            }
        }
        return $best_imp;
    };
    my $gen_decl = sub {
        my($symbol, $comment) = @_;
        no warnings 'uninitialized';
        my $imp = $var{$symbol} && $var{$symbol}{imp};
        if( $imp && $IMP{$imp}{decl} ) {
            $IMP{$imp}{decl}($symbol, $comment);
        } else {
            warn "can't gen_decl($symbol) [$imp] ($comment)";
            push @XS, "// can't gen_decl($symbol) [$imp] ($comment)";
        }
    };
    my $gen_const = sub {
        my($symbol, $value) = @_;
        my $imp = $var{$symbol} && $var{$symbol}{imp};
        if( $imp && $IMP{$imp}{const} ) {
            $IMP{$imp}{const}($symbol, $value);
        } else {
            warn "can't gen_const($symbol) [$imp]";
            push @XS, "// can't gen_const($symbol) [$imp]";
        }
    };
    my $gen_move = sub {
        my($from, $to) = @_;
        my $from_imp = $var{$from} && $var{$from}{imp};
        my $to_imp = $var{$to} && $var{$to}{imp};
        if( $from_imp && $to_imp && $IMP{$from_imp}{$to_imp} ) {
            $IMP{$from_imp}{$to_imp}($from, $to);
        } else {
            warn "can't gen_move($from, $to) [$from_imp, $to_imp]";
            push @XS, "// can't gen_move($from, $to) [$from_imp, $to_imp]";
        }
    };

    my %OP =
    ( nextstate =>
      { inf => sub {
            my($op) = @_;
            $stack[-1] = [[]];
            if( exists $op->{chain}{':'} && $op->{'~next'}{name} eq 'enterloop' ) {
                $op->{'~next'}{state_label} = $op->{chain}{':'};
                $op->{'~next'}{stack_len} = 0+@stack;
            }
            push @op_stack, $op->{'~next'};
        }
      , gen => sub {
            my($op) = @_;
            $stack[-1] = [[]];
            if( exists $op->{chain}{':'} && $op->{'~next'}{name} eq 'enterloop' ) {
                $op->{'~next'}{state_label} = $op->{chain}{':'};
                $op->{'~next'}{stack_len} = 0+@stack;
            }
            push @op_stack, $op->{'~next'};
        }
      }
    , unstack =>
      { inf => sub {
            my($op) = @_;
            #die "not implemented" if( $op->{special} );
            $stack[-1] = [[]];
            push @op_stack, $op->{'~next'};
        }
      , gen => sub {
            my($op) = @_;
            #die "not implemented" if( $op->{special} );
            $stack[-1] = [[]];
            push @op_stack, $op->{'~next'};
        }
      }
    , pushmark =>
      { inf => sub {
            my($op) = @_;
            push @{$stack[-1]}, [];
            push @op_stack, $op->{'~next'};
        }
      , gen => sub {
            my($op) = @_;
            push @{$stack[-1]}, [];
            push @op_stack, $op->{'~next'};
        }
      }
    , enterloop =>
      { inf => sub {
            my($op) = @_;
            push @{$op->{cx_inf}}, $op;
            push @op_stack, $op->{'~next'};
        }
      , gen => sub {
            my($op) = @_;
            push @{$op->{cx}}, $op;
            push @op_stack, $op->{'~next'};
        }
      }
    , leaveloop =>
      { inf => sub {
            my($op) = @_;
            pop @{$op->{cx_inf}};
            push @op_stack, $op->{'~next'};
        }
      , gen => sub {
            my($op) = @_;
            #push @XS, "$op->{cx}[-1]{label}_END:;";
            pop @{$op->{cx}};
            push @op_stack, $op->{'~next'};
        }
      }
    , enter =>
      { inf => sub {
            my($op) = @_;
            push @op_stack, $op->{'~next'};
        }
      , gen => sub {
            my($op) = @_;
            push @XS, "// not implemented";
            push @op_stack, $op->{'~next'};
        }
      }
    , leave =>
      { inf => sub {
            my($op) = @_;
            push @op_stack, $op->{'~next'};
        }
      , gen => sub {
            my($op) = @_;
            push @XS, "// not implemented";
            push @op_stack, $op->{'~next'};
        }
      }
    , leavesub =>
      { inf => sub {
            my($op) = @_;
            my $tid = $uid++;
            $var{"t$tid"} = {op => 'leavesub', input => ['ANY'], output => ['ANY']};
            $stack[-1][-1][-1]{get}("t$tid");
        }
      , gen => sub {
            my($op) = @_;
            my $tid = $uid++;
            $gen_decl->("t$tid");
            $gen_move->($stack[-1][-1][-1]{symbol}, "t$tid");
#            push @XS, "SV * t$tid;";
#            $stack[-1][-1][-1]{get}("t$tid");
            push @XS
                , "XPUSHs(t$tid);"
                , "goto L_END;"
                ;
        }
      }
    , last =>
      { inf => sub {
            my($op) = @_;
            if( exists $op->{target_label} ) {
                while( $op->{cx_inf}[-1] && $op->{cx_inf}[-1]{state_label} ne $op->{target_label} ) {
                    pop @{$op->{cx_inf}};
                }
            }
            my $cx = pop @{$op->{cx_inf}};
            splice @stack, $cx->{stack_len}, -1, ();
            $stack[-1] = [[]];
            push @op_stack, $cx->{'~lastop'};
        }
      , gen => sub {
            my($op) = @_;
            if( exists $op->{target_label} ) {
                while( $op->{cx}[-1] && $op->{cx}[-1]{state_label} ne $op->{target_label} ) {
                    pop @{$op->{cx}};
                }
            }
            my $cx = pop @{$op->{cx}};
            splice @stack, $cx->{stack_len}, -1, ();
            $stack[-1] = [[]];
            push @op_stack, $cx->{'~lastop'};
        }
      }
    , aassign =>
      { inf => sub {
            my($op) = @_;
            my @outcome;
            for my $i (0..$#{$stack[-1][-1]}) {
                my $l = $stack[-1][-1][$i];
                my $r = $stack[-1][-2][$i];
                if( $r ) {
                    my $tid = $uid++;
                    $var{"t$tid"} = {op => 'aassign', input => [], output => []};
                    $r->{get}("t$tid");
                    $l->{put}("t$tid");
                } else {
                    $l->{put}("DEF");
                }
                push @outcome, $l;
            }
            splice @{$stack[-1]}, -2, 2, \@outcome;
            push @op_stack, $op->{'~next'};
        }
      , gen => sub {
            my($op) = @_;
            my @outcome;
            for my $i (0..$#{$stack[-1][-1]}) {
                my $l = $stack[-1][-1][$i];
                my $r = $stack[-1][-2][$i];
                if( $r ) {
                    my $tid = $uid++;
                    $gen_decl->("t$tid");
                    $gen_move->($r->{symbol}, "t$tid");
                    $gen_move->("t$tid", $l->{symbol});
#                    push @XS, "SV * t$tid;";
#                    $r->{get}("t$tid");
#                    $l->{put}("t$tid");
                } else {
                    $gen_const->($l->{symbol}, undef);
#                    $l->{put}("&PL_sv_undef");
                }
                push @outcome, $l;
            }
            splice @{$stack[-1]}, -2, 2, \@outcome;
            push @op_stack, $op->{'~next'};
        }
      }
    , sassign =>
      { inf => sub {
            my($op) = @_;
            if( $op->{set_module_sub} ) {
                $abort = __LINE__;
                return;
            }
            my($l, $r) = $op->{flip_args} ? @{$stack[-1][-1]}[-2,-1] : @{$stack[-1][-1]}[-1,-2];

            my $tid = $uid++;
            $var{"t$tid"} = {op => 'sassign', input => [], output => []};
            $r->{get}("t$tid");
            $l->{put}("t$tid");
            splice @{$stack[-1][-1]}, -2, 2, $l;
            push @op_stack, $op->{'~next'};
        }
      , gen => sub {
            my($op) = @_;
            if( $op->{set_module_sub} ) {
                $abort = __LINE__;
                return;
            }
            my($l, $r) = $op->{flip_args} ? @{$stack[-1][-1]}[-2,-1] : @{$stack[-1][-1]}[-1,-2];

            my $tid = $uid++;
            $gen_decl->("t$tid");
            $gen_move->($r->{symbol}, "t$tid");
            $gen_move->("t$tid", $l->{symbol});
#            push @XS, "SV * t$tid;";
#            $r->{get}("t$tid");
#            $l->{put}("t$tid");
            splice @{$stack[-1][-1]}, -2, 2, $l;
            push @op_stack, $op->{'~next'};
        }
      }
    , padrange =>
      { inf => sub {
            my($op) = @_;
            my $count = $op->{count};
            my $offset = $op->{offset};
            if( $op->{my} ) {
                for my $i ($offset .. $offset+$count-1) {
                    $var{"pad$i"} = {op => 'padrange', input => [], output => [], var => $op->{var}[$i-$offset]};
                }
            }
            if( $op->{special} ) {
                push @{$stack[-1]}, [];
                for my $i (0 .. $count-1) {
                    push @{$stack[-1][-1]},
                      { put => sub {
                            my($symbol) = @_;
                            push @{$var{$symbol}{output}}, 'ANY';
                        }
                      , get => sub {
                            my($symbol) = @_;
                            push @{$var{$symbol}{input}}, 'ANY';
                        }
                      };
                }
            }
            push @{$stack[-1]}, [];
            for my $i ($offset .. $offset+$count-1) {
                push @{$stack[-1][-1]},
                  { put => sub {
                        my($symbol) = @_;
                        push @{$var{$symbol}{output}}, "pad$i";
                        push @{$var{"pad$i"}{input}}, $symbol;
                    }
                  , get => sub {
                        my($symbol) = @_;
                        push @{$var{"pad$i"}{output}}, $symbol;
                        push @{$var{$symbol}{input}}, "pad$i";
                    }
                  };
            }
            push @op_stack, $op->{'~next'};
        }
      , gen => sub {
            my($op) = @_;
            my $count = $op->{count};
            my $offset = $op->{offset};
            if( $op->{my} ) {
                for my $i ($offset .. $offset+$count-1) {
                    $gen_decl->("pad$i", $op->{var}[$i-$offset]);
#                    push @XS, "SV * pad$i = newSV(0); // $op->{var}[$i-$offset]";
                }
            }
            if( $op->{special} ) {
                push @{$stack[-1]}, [];
                for my $i (0 .. $count-1) {
                    $var{"ST($i)"}{imp} = 'ANY';
                    push @{$stack[-1][-1]}, {symbol => "ST($i)"};
#                      { put => sub {
#                            my($symbol) = @_;
#                            push @XS, "SvSetSV(ST($i), $symbol);";
#                        }
#                      , get => sub {
#                            my($symbol) = @_;
#                            push @XS, "$symbol = ST($i);";
#                        }
#                      };
                }
            }
            push @{$stack[-1]}, [];
            for my $i ($offset .. $offset+$count-1) {
                push @{$stack[-1][-1]}, {symbol => "pad$i"};
#                  { put => sub {
#                        my($symbol) = @_;
#                        push @XS, "SvSetSV(pad$i, $symbol);";
#                    }
#                  , get => sub {
#                        my($symbol) = @_;
#                        push @XS, "$symbol = pad$i;";
#                    }
#                  };
            }
            push @op_stack, $op->{'~next'};
        }
      }
    , padsv =>
      { inf => sub {
            my($op) = @_;
            my $i = $op->{offset};
            if( $op->{my} ) {
                $var{"pad$i"} = {op => 'padsv', input => [], output => [], var => $op->{var}};
            }
            push @{$stack[-1][-1]},
              { put => sub {
                    my($symbol) = @_;
                    push @{$var{$symbol}{output}}, "pad$i";
                    push @{$var{"pad$i"}{input}}, $symbol;
                }
              , get => sub {
                    my($symbol) = @_;
                    push @{$var{"pad$i"}{output}}, $symbol;
                    push @{$var{$symbol}{input}}, "pad$i";
                }
              };
            push @op_stack, $op->{'~next'};
        }
      , gen => sub {
            my($op) = @_;
            my $i = $op->{offset};
            if( $op->{my} ) {
                $gen_decl->("pad$i", $op->{var});
#                push @XS, "SV * pad$i = newSV(0); // $op->{var}";
            }
            push @{$stack[-1][-1]}, {symbol => "pad$i"};
#              { put => sub {
#                    my($symbol) = @_;
#                    push @XS, "SvSetSV(pad$i, $symbol);";
#                }
#              , get => sub {
#                    my($symbol) = @_;
#                    push @XS, "$symbol = pad$i;";
#                }
#              };
            push @op_stack, $op->{'~next'};
        }
      }
    , const =>
      { inf => sub {
            my($op) = @_;
            my $tid = $uid++;
            $var{"t$tid"} = {op => 'const', input => [], output => []};
            if( !defined $op->{value} ) {
                push @{$var{"t$tid"}{input}}, 'DEF';
            } elsif( $op->{value} =~ /\A[01]\z/ ) {
                push @{$var{"t$tid"}{input}}, 'BOOL';
            } elsif( $op->{value} == int $op->{value} ) {
                push @{$var{"t$tid"}{input}}, 'INT';
            } else {
                push @{$var{"t$tid"}{input}}, 'STR';
            }
            push @{$stack[-1][-1]},
              { put => sub {
                    my($symbol) = @_;
                    warn "???";
                }
              , get => sub {
                    my($symbol) = @_;
                    push @{$var{"t$tid"}{output}}, $symbol;
                    push @{$var{$symbol}{input}}, "t$tid";
#                    if( $op->{value} =~ /[01]/ ) {
#                        push @{$var{$symbol}{input}}, 'BOOL';
#                    } elsif( $op->{value} =~ /\A-?\d+\z/ ) {
#                        push @{$var{$symbol}{input}}, 'INT';
#                    } else {
#                        push @{$var{$symbol}{input}}, 'ANY';
#                    }
                }
              };
            push @op_stack, $op->{'~next'};
        }
      , gen => sub {
            my($op) = @_;
            my $tid = $uid++;
            $gen_decl->("t$tid");
            $gen_const->("t$tid", $op->{value});
            push @{$stack[-1][-1]}, {symbol => "t$tid"};
#              { put => sub {
#                    my($symbol) = @_;
#                }
#              , get => sub {
#                    my($symbol) = @_;
#                    push @XS, "$symbol = sv_2mortal(newSViv($op->{value}));";
#                }
#              };
            push @op_stack, $op->{'~next'};
        }
      }
    , int =>
      { inf => sub {
            my($op) = @_;
            my $tid = $uid++;
            my $rid = $uid++;
            $var{"t$tid"} = {op => 'int', input => [], output => ['INT']};
            $var{"t$rid"} = {op => 'int', input => ['INT'], output => []};
            $stack[-1][-1][-1]{get}("t$tid");
            $stack[-1][-1][-1] =
              { put => sub {
                    my($symbol) = @_;
                    warn "???";
                }
              , get => sub {
                    my($symbol) = @_;
                    push @{$var{"t$rid"}{output}}, $symbol;
                    push @{$var{$symbol}{input}}, "t$rid";
                }
              };
            push @op_stack, $op->{'~next'};
        }
      , gen => sub {
            my($op) = @_;
            my $tid = $uid++;
            my $rid = $uid++;
            $gen_decl->("t$tid");
            $gen_decl->("t$rid");
            $gen_move->($stack[-1][-1][-1]{symbol}, "t$tid");
            $gen_move->("t$tid", "t$rid");
            $stack[-1][-1][-1] = {symbol => "t$rid"};
            push @op_stack, $op->{'~next'};
        }

      }
    , ( map {
        my($name, $operator, $operand_type, $result_type, $rule_gen) = @$_;
        ( $name =>
          { inf => sub {
                my($op) = @_;
                my $a = 't'.$uid++;
                my $b = 't'.$uid++;
                my $o = $op->{target_at} eq 'stack' ? 't'.$uid++ : 'pad'.$op->{op_targ};
                my @extra_rule = $rule_gen ? ($rule_gen->($a, $b, $o)) : ();
                $var{$a} = {op => $name, input => [], output => $operand_type, extra_rule => [@extra_rule]};
                $var{$b} = {op => $name, input => [], output => $operand_type, extra_rule => [@extra_rule]};
                $stack[-1][-1][-2]{get}($a);
                $stack[-1][-1][-1]{get}($b);

                if( exists($var{$o}) ) {
                    push @{$var{$o}{input}}, @$result_type;
                } else {
                    $var{$o} = {op => $name, input => $result_type, output => [], extra_rule => [@extra_rule]};
                }
                if( $op->{target_at} eq 'stack' ) {
                    $stack[-1][-1][-2]{put}($o);
                } else {
                    $stack[-1][-1][-2] =
                      { put => sub {
                            my($symbol) = @_;
                            warn "???";
                            #push @{$var{$o}{input}}, $symbol;
                            #push @{$var{$symbol}{output}}, $o;
                        }
                      , get => sub {
                            my($symbol) = @_;
                            push @{$var{$symbol}{input}}, $o;
                            push @{$var{$o}{output}}, $symbol;
                        }
                      };
                }
                pop @{$stack[-1][-1]};
                push @op_stack, $op->{'~next'};
            }
          , gen => sub {
                my($op) = @_;
                my $a = 't'.$uid++;
                my $b = 't'.$uid++;
                my $o = $op->{target_at} eq 'stack' ? 't'.$uid++ : 'pad'.$op->{op_targ};

                $gen_decl->($a);
                $gen_move->($stack[-1][-1][-2]{symbol}, $a);

                $gen_decl->($b);
                $gen_move->($stack[-1][-1][-1]{symbol}, $b);

                if( $var{$o}{op} eq $name ) {
                    $gen_decl->($o);
                }

                local @var{qw(a_int b_int o_int a_num b_num o_num)} = (({imp => 'INT'})x3, ({imp => 'NUM'})x3);
                my $static_type = 'INT';
                for my $v ($a, $b) {
                    my %int_det = (
                        BOOL => 1,
                        INT => 1,
                        NUM => 0,
                        INTNUM => "$v.INT!=IV_MIN",
                    );
                    my $expr = $int_det{$var{$v}{imp}};
                    push @XS, qq(int $v\_is_int = $expr; // $var{$v}{imp});
                    $static_type = 'NUM' if( $expr eq '0' );
                    $static_type = '' if( $static_type eq 'INT' && $expr ne '1' );
                }
                push @XS, "if( $a\_is_int && $b\_is_int ){";
                if( $static_type ne 'NUM' ) {
                    push @XS, "  IV a_int, b_int, o_int;";
                    $gen_move->($a, "a_int");
                    $gen_move->($b, "b_int");
                    push @XS, "  o_int = a_int $operator b_int;";
                    $gen_move->("o_int", $o);
                }
                push @XS, "}else{";
                if( $static_type ne 'INT' ) {
                    push @XS, "  NV a_num, b_num, o_num;";
                    $gen_move->($a, "a_num");
                    $gen_move->($b, "b_num");
                    push @XS, "  o_num = a_num $operator b_num;";
                    $gen_move->("o_num", $o);
                }
                push @XS, "}";
#                push @XS, "SV *t$a, *t$b;";
#                $stack[-1][-1][-2]{get}("t$a");
#                $stack[-1][-1][-1]{get}("t$b");
#                push @XS, "SV *t$o = sv_2mortal(newSViv(SvIV(t$a) $operator SvIV(t$b)));";
                if( $op->{target_at} eq 'stack' ) {
                    $gen_move->($o, $stack[-1][-1][-2]{symbol});
#                    $stack[-1][-1][-2]{put}("t$o");
                } else {
                    $stack[-1][-1][-2] = {symbol => $o};
#                      { put => sub {
#                            my($symbol) = @_;
#                            push @XS, "SvSetSV(t$o, $symbol);";
#                        }
#                      , get => sub {
#                            my($symbol) = @_;
#                            push @XS, "$symbol = t$o;";
#                        }
#                      };
                }
                pop @{$stack[-1][-1]};
                push @op_stack, $op->{'~next'};
            }
          }
        );
      } ( [ ge => '>=', ['INT', 'NUM'], ['BOOL'],
            sub { my($ta, $tb, $to) = @_; sub {
                $var{$tb}{type} = 'NUM' if( $best_imp->($ta) eq 'NUM' );
                $var{$ta}{type} = 'NUM' if( $best_imp->($tb) eq 'NUM' );
            } }
          ]
        , [ gt => '>', ['INT', 'NUM'], ['BOOL'],
            sub { my($ta, $tb, $to) = @_; sub {
                $var{$tb}{type} = 'NUM' if( $best_imp->($ta) eq 'NUM' );
                $var{$ta}{type} = 'NUM' if( $best_imp->($tb) eq 'NUM' );
            } }
          ]
        , [ eq => '==', ['INT', 'NUM'], ['BOOL'],
            sub { my($ta, $tb, $to) = @_; sub {
                $var{$tb}{type} = 'NUM' if( $best_imp->($ta) eq 'NUM' );
                $var{$ta}{type} = 'NUM' if( $best_imp->($tb) eq 'NUM' );
            } }
          ]
        , [ lt => '<', ['INT', 'NUM'], ['BOOL'],
            sub { my($ta, $tb, $to) = @_; sub {
                $var{$tb}{type} = 'NUM' if( $best_imp->($ta) eq 'NUM' );
                $var{$ta}{type} = 'NUM' if( $best_imp->($tb) eq 'NUM' );
            } }
          ]
        , [ le => '<=', ['INT', 'NUM'], ['BOOL'],
            sub { my($ta, $tb, $to) = @_; sub {
                $var{$tb}{type} = 'NUM' if( $best_imp->($ta) eq 'NUM' );
                $var{$ta}{type} = 'NUM' if( $best_imp->($tb) eq 'NUM' );
            } }
          ]
        , [ add => '+', ['INT', 'NUM'], ['INT', 'NUM'],
            sub { my($ta, $tb, $to) = @_; sub {
                $var{$tb}{type} = 'NUM' if( $best_imp->($ta) eq 'NUM' );
                $var{$ta}{type} = 'NUM' if( $best_imp->($tb) eq 'NUM' );
            } }
          ]
        , [ subtract => '-', ['INT', 'NUM'], ['INT', 'NUM'],
            sub { my($ta, $tb, $to) = @_; sub {
                $var{$tb}{type} = 'NUM' if( $best_imp->($ta) eq 'NUM' );
                $var{$ta}{type} = 'NUM' if( $best_imp->($tb) eq 'NUM' );
            } }
          ]
        , [ modulo => '%', ['INT'], ['INT'],
          ]
        , [ bit_xor => '^', ['INT'], ['INT'],
          ]
        )
      )
    , preinc =>
      { inf => sub {
            my($op) = @_;
            my $t = $uid++;
            $var{"t$t"} = {op => 'preinc', input => [], output => []};
            $stack[-1][-1][-1]{get}("t$t");
            $stack[-1][-1][-1]{put}("t$t");
            for my $dir (qw(input output)) {
#                @{$var{"t$t"}{$dir}} = map { [(ref($_) ? @$_ : $_), ['INT','STR']] } @{$var{"t$t"}{$dir}};
                @{$var{"t$t"}{$dir}} = map { [(ref $_ ? @$_ : $_), 'INT'] } @{$var{"t$t"}{$dir}};
            }
            push @op_stack, $op->{'~next'};
        }
      , gen => sub {
            my($op) = @_;
            my $t = $uid++;
            $gen_decl->("t$t");
            $gen_move->($stack[-1][-1][-1]{symbol}, "t$t");
            if( $var{"t$t"}{imp} eq 'INT' ) {
                push @XS, "++t$t;";
            } else {
                push @XS, "sv_int(t$t);";
            }
            $gen_move->("t$t", $stack[-1][-1][-1]{symbol});
#            push @XS, "SV * t$t;";
#            $stack[-1][-1][-1]{get}("t$t");
#            push @XS, "sv_inc(t$t);";
            push @op_stack, $op->{'~next'};
        }
      }
    , and =>
      { inf => sub {
            my($op) = @_;

            my $t = $uid++;
            $var{"t$t"} = {op => 'and', input => [], output => ['BOOL']};
            $stack[-1][-1][-1]{get}("t$t");

            push @op_stack
                , $op->{'~false'}
                , { gen => sub {
                    pop @{$stack[-1][-1]};
                } }
                , $op->{'~true'}
                ;
        }
      , gen => sub {
            my($op) = @_;

            my $t = $uid++;
            $gen_decl->("t$t");
            $gen_move->($stack[-1][-1][-1]{symbol}, "t$t");
            push @XS, "if( t$t ){";
#            push @XS, "SV *t$t;";
#            $stack[-1][-1][-1]{get}("t$t");
#            push @XS, "if( SvTRUE_NN(t$t) ){";

            push @op_stack
                , { gen => sub {
                    push @XS, "}";
                } }
                , $op->{'~false'}
                , { gen => sub {
                    push @XS, "} else {";
                    pop @{$stack[-1][-1]};
                } }
                , $op->{'~true'}
                ;
        }
      }
    , or =>
      { inf => sub {
            my($op) = @_;

            my $t = $uid++;
            $var{"t$t"} = {op => 'or', input => [], output => ['BOOL']};
            $stack[-1][-1][-1]{get}("t$t");

            push @op_stack
                , $op->{'~true'}
                , { gen => sub {
                    pop @{$stack[-1][-1]};
                } }
                , $op->{'~false'}
                ;
        }
      , gen => sub {
            my($op) = @_;

            my $t = $uid++;
            $gen_decl->("t$t");
            $gen_move->($stack[-1][-1][-1]{symbol}, "t$t");
            push @XS, "if( !t$t ){";
#            push @XS, "SV *t$t;";
#            $stack[-1][-1][-1]{get}("t$t");
#            push @XS, "if( !SvTRUE_NN(t$t) ){";

            push @op_stack
                , { gen => sub {
                    push @XS, "}";
                } }
                , $op->{'~true'}
                , { gen => sub {
                    push @XS, "} else {";
                    pop @{$stack[-1][-1]};
                } }
                , $op->{'~false'}
                ;
        }
      }
    );
    while(my($name, $op) = each %OP) {
        $op->{name} = $name;
    }

    ###########################
    # assign type

    $op_chain->{cx_inf} //= [];
    push @op_stack, $op_chain;
    while(my $op = pop @op_stack) {
        if( $op->{state} eq 'inf' ) {
            next;
        }
        $op->{state} = 'inf';
        if( $op->{inf} || $OP{$op->{name}}{inf} ) {
            ($op->{inf} // $OP{$op->{name}}{inf})->($op);
        }
        for my $o (@op_stack) {
            $o->{cx_inf} //= [@{$op->{cx_inf}}];
        }
    }
    for my $var (values %var) {
        $var->{type} = ['ANY'];
    }
    for(my $changed=1; $changed; ) {
        $changed = 0;
        for my $var (values %var) {
            my $ext_inter;
            my $ext_union = sub {
                my($root) = @_;
                if( ref($root) ) {
                    return [ map { $ext_inter->($_) } @$root ]
                } else {
                    if( exists $var{$root} ) {
                        return $var{$root}{type};
                    } else {
                        return $root;
                    }
                }
            };
            $ext_inter = sub {
                my($root) = @_;
                if( ref($root) ) {
                    return [ map { $ext_union->($_) } @$root ]
                } else {
                    if( exists $var{$root} ) {
                        if( ref $var{$root}{type} ) {
                            return @{$var{$root}{type}};
                        } else {
                            return $var{$root}{type};
                        }
                    } else {
                        return $root;
                    }
                }
            };
            my $type_inter = sub {
                my($a, $b) = @_;
                for my $guess (qw(NONE DEF BOOL INT NUM STR REF ANY)) {
                    return $guess if( $a eq $guess || $b eq $guess );
                }
            };
            my $type_union = sub {
                my($a, $b) = @_;
            };
            my $flatten_inter; $flatten_inter = sub {
                #print "flatten_inter(", Dumper(\@_), ")\n";
                my @term = map { ref $_ ? [map { ref $_ ? $flatten_inter->(@$_) : $_ } @$_] : $_ } @_;
                #print "then ", Dumper(\@term), $/;
                my @out = ref $term[-1] ? @{pop @term} : pop @term;
                while(my $term = pop @term) {
                    if( ref $term ) {
                        @out = map { my $o = $_; map { $type_inter->($o, $_) } @$term } @out;
                    } else {
                        @out = map { $type_inter->($_, $term) } @out;
                    }
                }
                #print "got @{[uniqstr @out]}\n";
                return uniqstr @out;
            };
            my @eq = ($ext_union->($var->{input}), $ext_union->($var->{output}));
            #print "eq for ", Dumper($var), ' is ', Dumper(\@eq), $/;
            my @type = sort $flatten_inter->(@eq);
            #print "got ", Dumper(\@type),$/;
            if( join(',', @type) ne (ref $var->{type} ? join(',', @{$var->{type}}) : $var->{type}) ) {
                $var->{type} = @type>1 ? \@type : $type[0];
                $changed = 1;
                for my $rule ( @{$var->{extra_rule} // []} ) {
                    $rule->();
                }
            }
            undef $flatten_inter;
            undef $ext_inter;
            undef $ext_union;
        }
    }
    for my $var (values %var) {
        $var->{imp} = $best_imp->($var->{type});
    }

    use Data::Dumper;
    $Data::Dumper::Indent =
    $Data::Dumper::Sortkeys =
    $Data::Dumper::Terse = 1;
    say 'var', Dumper(\%var);

    ###########################
    # gen code

    $uid = 0;
    @stack = ([[]]);

    $op_chain->{cx} //= [];
    push @op_stack, $op_chain;
    while(my $op = pop @op_stack) {
        if( $op->{state} eq 'gen' ) {
            push @XS, "goto $op->{label};";
            next;
        }
        if( !$op->{gen} && !$OP{$op->{name}}{gen} ) {
            push @XS, "// op $op->{name} without gen";
            next;
        }
        $op->{label} = 'L' . $label_uid++;
        push @XS, "$op->{label}:; // $op->{name}";
        $op->{state} = 'gen';
        ($op->{gen} // $OP{$op->{name}}{gen})->($op);
        for my $o (@op_stack) {
            $o->{cx} //= [@{$op->{cx}}];
        }
    }

    my $XS = join $/, map { "        $_" } @XS;
    $XS = <<~".";
    void
    $thing(...)
        PPCODE:
    $XS
            L_END:;

    .
    return $XS;
}

1;
__END__
# Below is stub documentation for your module. You'd better edit it!

=head1 NAME

Speedup - Perl extension for blah blah blah

=head1 SYNOPSIS

  use Speedup;
  blah blah blah

=head1 DESCRIPTION

Stub documentation for Speedup, created by h2xs. It looks like the
author of the extension was negligent enough to leave the stub
unedited.

Blah blah blah.

=head2 EXPORT

None by default.



=head1 SEE ALSO

Mention other useful documentation such as the documentation of
related modules or operating system documentation (such as man pages
in UNIX), or any relevant external documentation such as RFCs or
standards.

If you have a mailing list set up for your module, mention it here.

If you have a web site set up for your module, mention it here.

=head1 AUTHOR

A. U. Thor, E<lt>cindy@nonetE<gt>

=head1 COPYRIGHT AND LICENSE

Copyright (C) 2022 by A. U. Thor

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself, either Perl version 5.30.2 or,
at your option, any later version of Perl 5 you may have available.


=cut
