{
  pkgs ? import <nixpkgs> { }
}:

# To use: run `nix-shell` or `nix-shell --run "exec zsh"`
# https://nixos.org/wiki/Development_Environments
# http://nixos.org/nix/manual/#sec-nix-shell

let
  # Pin a nixpkgs version
  # Recent enough to include Coq 8.7
  pinned_pkgs = import (pkgs.fetchFromGitHub {
    owner  = "NixOS";
    repo   = "nixpkgs";
    rev    = "8abcedd90e22269e865dc03c657aaa54cb1aaf89";
    sha256 = "0k933011kw38vc32v6cz9g29fzr4bzmc9g294qs3wmnpcd0vh0dg";
  }) { };

  ### Dependencies
  coq = pinned_pkgs.coq_8_7;

in with pinned_pkgs; stdenv.mkDerivation {
  name = "coq${coq.coq-version}-unimath";
  src = if lib.inNixShell then null else ./.;
  buildInputs = [ coq coq.ocaml coq.camlp5 ];
  enableParallelBuilding = true;
  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

  shellHook = ''
    export COQBIN=${coq}/bin
    export COQLIB=${coq}/lib/coq
    export COQC=${coq}/bin/coqc
    export COQDEP=${coq}/bin/coqdep
    exec zsh
  '';

  meta = with stdenv.lib; {
    homepage = https://github.com/siddharthist/UniMath;
    # description = "";
    maintainers = with maintainers; [ siddharthist ];
    platforms = coq.meta.platforms;
  };
}
