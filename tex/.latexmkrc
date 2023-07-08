# Use subroutine to do preprocessing and running pdflatex
$pdflatex = 'internal mylatex %B %O';
sub mylatex {
  my $base = shift @_;
  my $tex = "$base.tex";
  my $lhs = "$base.lhs";

  # Run the preprocessor
  system('lhs2TeX', '--agda', '-o', 'agda-lhs2tex.sty', 'agda-lhs2tex.lhs') == 0 or return $?;
  system('lhs2TeX', '--agda', '-o', 'sec6-formalisation.tex', 'sec6-formalisation.lhs') == 0 or return $?;
  
  #if (-e $lhs) { system('lhs2TeX', '--agda', '-o', $tex, "$lhs") == 0 or return $?; }
  #opendir(my $dh, '.') or die;
  #while (my $filename = readdir($dh)) {
  #  next unless ($filename =~ /\.lhs$/i);  # Check for files with .lhs extension
  #  next if (-d "$directory/$filename");   # Skip directories
  #  my $fp = fileparse($filename, qr/\.[^.]*/);
  #  system('lhs2TeX', '--agda', '-o', "$fp.tex", "$fp.lhs") == 0 or return $?;
  #}

  # Run pdflatex
  my $return = system('pdflatex', @_, $tex);

  #if (-e $lhs) {system "echo INPUT $base.lhs >> $aux_dir1$base.fls";}

  #  opendir(my $dh, '.') or die;
  #  while (my $filename = readdir($dh)) {
  #    next unless ($filename =~ /\.lhs$/i);  # Check for files with .lhs extension
  #    next if (-d "$directory/$filename");   # Skip directories
  #    my $fp = fileparse($filename, qr/\.[^.]*/);
  #    system "echo INPUT $fp.lhs >> $aux_dir1$base.fls";
  #  }
  #
  system "echo INPUT agda.fmt >> $aux_dir1$base.fls";
  system "echo INPUT sec6-formalisation.lhs >> $aux_dir1$base.fls";
  return $return;
}
