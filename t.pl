use strict;
use warnings;
use feature qw(say);
use blib;
use Speedup;
use Data::Dumper;
$Data::Dumper::Indent = $Data::Dumper::Sortkeys = $Data::Dumper::Terse = 1;

sub gcd {
    my($a, $b, $h) = (@_, 20);
    while($a) {
        $a ^= $b ^= $a ^= $b %= $a;
    }
    if( $a ) {
        $h = 3;
    } else {
        $h = 2;
    }
    for(my $i=0; $i<10; ++$i) {
        $a += int $i;
    }
    return $b-$a;
}

sub try {
    my($a, $b) = map { int rand $_ } (1000, 1000);
    my $gcd = gcd($a, $b);
    say "gcd($a, $b) = $gcd";
}

for(1..10) {
#    try();
}

my $op_chain = Speedup::op_chain(\&gcd);
say Dumper($op_chain);
Speedup::destroy_op_chain($op_chain);
