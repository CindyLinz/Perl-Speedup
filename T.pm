#package T;
use strict;
use warnings;
use feature qw(say);
use blib;
use Speedup;
use Data::Dumper;
use Time::HiRes qw(time);
$Data::Dumper::Indent = $Data::Dumper::Sortkeys = $Data::Dumper::Terse = 1;

use Inline Config =>
    clean_after_build => 0,
    clean_build_area => 1,
    force_build => 1;
#use Inline C => config => optimize => '-O0';
#use Inline 'Speedup' => 'gcd';
#Inline->bind('Speedup' => 'gcd count_factor');
Inline->bind('Speedup' => 'gcd count_factor', optimize => '-O3');
#Inline->bind('Speedup' => 'gcd');

sub gcd {
    #my($a, $b, $h, @x, %y) = (@_, 20);
    #local $_[1]{bc}{d}[234][2]; # = 2;
    #$x[$a][4][20][$b]{$h} = 5;
    my($a, $b) = (@_);
    #my $y = $a + $b;
    #my $x = ($a, $b) = (3, 4);
    OUTER: while(1) {
               {
            last OUTER if( !$a );
            $a = $a ^ ($b ^= $a ^= $b %= $a);
               }
    }
#    if( $a ) {
#        $h = 3;
#    } else {
#        $h = 2;
#    }
#    for(my $i=0; $i<10; ++$i) {
#        $a += int $i;
#    }
    #return $b-$a;
    return $b;
}

sub try {
    my($a, $b) = map { int rand $_ } (100, 100);
    my $gcd = gcd($a, $b);
    say "gcd($a, $b) = $gcd";
}

for(1..10) {
    try();
}

sub count_factor {
    my($n) = @_;
    my $n_ = int $n;
    my $ans = 0;
    for(my $i=1; $i<=$n_; ++$i) {
    #for(my $i=1; $i<=$n_; $i=$i+1) {
        if( $n_ % $i == 0 ) {
            ++$ans;
        }
    }
    return $ans;
}

sub try_count_factor {
    my $n = $_[0];
    my $btime = time;
    my $ans = count_factor($n);
    my $etime = time;
    my $time = $etime - $btime;
    print "# of factors of $n is $ans in $time seconds\n";
}

#for(10, 20, 1000, 10000, 1048576, 16777216, 67108864, 671088640) {
for(10, 20, 1000, 10000, 1048576, 16777216, 67108864) {
    try_count_factor($_);
}

#sub sqr { $_[0] * $_[0] }

#say sqr(30);

eval "sub xxx {}";

#my $op_chain = Speedup::op_chain(\&gcd);
#say Dumper($op_chain);
#Speedup::destroy_op_chain($op_chain);

1;
