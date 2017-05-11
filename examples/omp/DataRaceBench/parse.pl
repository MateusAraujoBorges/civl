#!/usr/bin/perl
use Math::Round;

$output_file = $ARGV[0];

open(OUTPUT, "<", $output_file) || die "Could not open $output_file";

while ($line=<OUTPUT>) {
  my($name,$tag,$message,$result);

  chomp($line);
  next unless ($line =~/^Check data race for/);
  ($name) = ($line =~/^Check data race for (.*)$/);
  $tag  = -1;
  if ($name =~ /yes.c$/) {
      $tag = 1; # 1 for data race
  } elsif ($name =~ /-no.c$/) {
      $tag = 0; # 0 for free of data race
  }
  ## checking if printed lines are expected:
  $line=<OUTPUT>;
  chomp($line);
  ($line =~ /^civl verify/) || die "Unexpected line after reading the name of the benchmark.";
  $line=<OUTPUT>;
  chomp($line);
  ($line =~ /^CIVL v1.8\+ of/) || die "Unexpected line after echoing the command";
  $line=<OUTPUT>;
  chomp($line);
  if (($line =~ /^Error:/) || ($line =~ /^Exception in thread/)) {
      $result = "E";
  } elsif ($line =~ /^Possible data race under/) {
      ## static analyzer caught error
      if ($tag == 1) {
	  $result = "P"
      } elsif ($tag == 0) {
	  $result = "N"; 
      } else {
	  die "Invalid tag though static analyzer catch error for $name at $line";
      }
  } else {
      ## look for civl results:
      while ($line=<OUTPUT>) {
	  if ($line =~ /^CIVL execution violation/) {
	      $message = $line,"\n",<OUTPUT>;
	  }
	  next unless ($line =~ /^=== Result ===/);
	  $line=<OUTPUT>;
	  if ($line =~ /^The standard properties hold for all executions.$/) {
	      $result = $tag == 0 ? "P (CIVL)" : "N";
	  } else {
	      $result = $tag == 1 ? "P (CIVL)" : "N";
	      ($line =~ /^The program MAY NOT be correct./) || die "Irregular CIVL output for false benchmarks: $line";
	  }
	  last;
      }
  }

  die "no name" unless defined($name);
  die "no tag" unless defined($tag);
  die "no result" unless defined($result);

  # for debugging:

  # print "name = $name\n";
  # print "cite = $cite\n";
  # print "type = $type\n";
  # print "scale = $scale\n";
  # print "loc = $loc\n";
  # print "prove = $prove\n";
  # print "mem = $mem\n";
  # print "time = $time\n";
  # print "states = $states\n"
  # print "transitions = $steps\n";
  # print "result = $result\n";
  # print "\n";

  printf("%-40s %s\n", $name, $result);
  if ($tag == 1 && $result == "P (CIVL)") {
      print $message, "\n";
  }
}
