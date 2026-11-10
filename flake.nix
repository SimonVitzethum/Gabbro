{
  # Gabbro as a Nix flake.
  #
  #   nix develop          a shell with everything the two guardians need: elan (Lean comes from each
  #                        package's `lean-toolchain`, so Lean and Mathlib stay pinned by the repository,
  #                        not by Nix), Python, git
  #
  # Lean is deliberately NOT taken from nixpkgs: `grammatik/`, `stage0/` and the other Lake packages pin their
  # exact toolchain and Mathlib revision, and one shared read-only Mathlib store serves every worktree.
  description = "Gabbro: a systems language whose safety guarantees are proved in Lean";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" ];
      forAll = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
    in
    {
      devShells = forAll (pkgs: {
        default = pkgs.mkShell {
          packages = [
            pkgs.elan
            pkgs.python3
            pkgs.git
            pkgs.curl
          ];
          # A leaked ELAN_TOOLCHAIN rebuilds everything under the wrong Lean (AGENTS.md section 9).
          shellHook = ''
            unset ELAN_TOOLCHAIN
          '';
        };
      });
    };
}
