{ stdenv, fetchurl, coq, ssreflect }:

stdenv.mkDerivation rec {
  name = "coq${coq.coq-version}-constructive-regexp-${version}";
  version = "2013-12-07";

  src = fetchurl {
    url = "https://www.ps.uni-saarland.de/~doczkal/regular/ConstructiveRegularLanguages-2013-12-07.tgz";
    sha256 = "41e33914b37d8b744a4deaa1ca3ac4fe392b29bfb57aca2e24e1777eb1f4dfd5";
  };

  buildInputs = [
  ];

  propagatedBuildInputs = [
    coq
    ssreflect
  ];

  patches = [
    ./fix-ssreflect-paths.patch
  ];

  unpackPhase = ''
    mkdir regexp
    tar -C regexp -xvzf $src
    cd regexp
  '';

  configurePhase = "coq_makefile -f Make -o Makefile";

  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

  meta = {
    description = "A  Constructive Theory of Regular Languages in Coq";
    maintainers = [
      "Christian Doczkal"
      "Jan-Oliver Kaiser"
      "Gert Smolka"
    ];
  };
}
