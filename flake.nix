{
  description = "diva";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05";

  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAllSystems = f:
        nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
    in {
      devShells = forAllSystems (pkgs: {
        default = pkgs.mkShell {
          # `elan` manages the Lean toolchain pinned in ./lean-toolchain
          # `git` is needed by Lake to fetch the ParseIt dependency.
          packages = [ pkgs.elan pkgs.git ];
        };
      });
    };
}
