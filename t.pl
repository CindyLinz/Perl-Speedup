use strict;
use warnings;
use feature qw(say);
use blib;
use Speedup;

sub gcd {
    my($a, $b) = @_;
    while($a) {
        $a ^= $b ^= $a ^= $b %= $a;
    }
    return $b;
}

sub try {
    my($a, $b) = map { int rand $_ } (1000, 1000);
    my $gcd = gcd($a, $b);
    say "gcd($a, $b) = $gcd";
}

for(1..10) {
    try();
}
