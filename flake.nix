{
  description = "The real numbers in Wiz";

  inputs = {
    # The Wiz toolchain (wiz, grail, the standard library). flake.lock pins the commit;
    # `wiz-toolchain` names the same commit for tower users.
    wiz.url = "github:wiz-pl/wiz/4ad297923dc74afbc7fd1e37ee2ae6f554c40783";
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
