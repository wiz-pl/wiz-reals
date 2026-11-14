{
  description = "The real numbers in Wiz";

  inputs = {
    # The Wiz toolchain (wiz, grail, the standard library). flake.lock pins the commit;
    # `wiz-toolchain` names the same commit for tower users.
    wiz.url = "github:wiz-pl/wiz/50cd3e7691dd7e63ff72c33aa24b68a032179c8d";
    # The same nixpkgs as the toolchain, so its binaries are shared.
    nixpkgs.follows = "wiz/nixpkgs";
  };

  outputs = { self, nixpkgs, wiz }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" ];
      forAll = f: nixpkgs.lib.genAttrs systems (system: f system nixpkgs.legacyPackages.${system});
    in {
      devShells = forAll (system: pkgs: {
        default = pkgs.mkShell {
          packages = [ wiz.packages.${system}.wiz ];   # wiz and grail
        };
      });
    };
}
