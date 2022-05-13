{ pkgs ? import <nixpkgs> { } }:

pkgs.mkShell {
  buildInputs = [
    pkgs.ocaml
    pkgs.opam

    pkgs.ocamlPackages.findlib
    pkgs.ocamlPackages.ocamlbuild
    pkgs.ocamlPackages.batteries
    pkgs.ocamlPackages.ocamlgraph
    pkgs.ocamlPackages.num
    pkgs.ocamlPackages.yojson
    pkgs.ocamlPackages.zarith
    pkgs.ocamlPackages.z3

    pkgs.z3

    pkgs.gnum4
    pkgs.gnumake

    # pkgs.solc-select
    pkgs.solc
  ];
}
