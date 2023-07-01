# Use subroutine to do preprocessing and running pdflatex
$pdflatex = 'internal mylatex %B %O';
sub mylatex {
  my $base = shift @_;
  my $tex = "$base.tex";
  my $lhs = "$base.lhs";

  # Run the preprocessor
  if (-e $lhs) { system('lhs2TeX', '--agda', '-o', $tex, "$lhs") == 0 or return $?; }
  # Run pdflatex
  my $return = system('pdflatex', @_, $tex);
  if (-e $lhs) {system "echo INPUT $base.lhs >> $aux_dir1$base.fls";}
  return $return;
}
