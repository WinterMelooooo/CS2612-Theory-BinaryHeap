#!/usr/bin/env perl

use v5.35;
use File::Basename;

if (@ARGV < 3) {
    die "usage: spp.perl <input-file> <new-header(relative to input-file)> <output-file(relative to input-file)>";
}

my $input = $ARGV[0];
my $header = $ARGV[1];
my $output = $ARGV[2];
my $cpp = "cpp";
if (@ARGV >= 4) {
    $cpp = $ARGV[3];
}

my $input_dir = dirname($input);
my $temp = $input_dir . "/.__temp__";
$output = $input_dir . "/" . $output;
my $relative_header = $header;
$header = $input_dir . "/" . $header;

if (open(my $temp_file, "<", $temp)) {
    close $temp_file;
    die "error: temporary file $temp already exists";
}

open(my $input_file, "<", $input) or die "$input: $!";
open(my $temp_file, ">", $temp) or die "$temp: $!";
open(my $output_file, ">", $output) or die "$output: $!";

while (<$input_file>) {
    if (/#include "(.*)"/) {
        print $temp_file "#include \"$1\"\n";
    }
}
close $input_file;
close $temp_file;

system($cpp, "-C", "-P", $temp, $header);

unlink $temp;

open($input_file, "<", $input);

my $first = 1;
while (<$input_file>) {
    if (/#include "(.*)"/) {
        if ($first) {
            print $output_file "#include \"$relative_header\"\n";
            $first = 0;
        }
    } else {
        print $output_file $_;
    }
}

close $input_file;
close $output_file;

print "bye\n"
