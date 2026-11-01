{
  # Gabbro as a Nix flake.
  #
  #   nix build            the `gabbro` command (checker, Stage-0 tools, LLVM driver), wrapped so that
  #                        `opt`, `llc` and `ld.lld` of the pinned LLVM are on its PATH
  #   nix run . -- hilfe   run it
  #   nix develop          a shell with everything the four guardians need: Rust, elan (Lean comes from
  #                        each package's `lean-toolchain`, so Lean and Mathlib stay pinned by the repository,
  #                        not by Nix), LLVM (opt, llc) and lld, qemu-user for the aarch64 runs, Python, git
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
      packages = forAll (pkgs:
        let
          llvm = pkgs.llvmPackages_latest;
          gabbro = pkgs.rustPlatform.buildRustPackage {
            pname = "gabbro";
            version = "0.0.1";
            src = pkgs.lib.fileset.toSource {
              root = ./.;
              fileset = pkgs.lib.fileset.unions [ ./Cargo.toml ./Cargo.lock ./crates ];
            };
            cargoLock.lockFile = ./Cargo.lock;
            cargoBuildFlags = [ "-p" "gabbro-cli" ];
            # The test suite drives Lean (`gabbro prove`) and the guardians; it runs in `nix develop`.
            doCheck = false;
            nativeBuildInputs = [ pkgs.makeWrapper ];
            postInstall = ''
              wrapProgram $out/bin/gabbro --prefix PATH : ${pkgs.lib.makeBinPath [ llvm.llvm llvm.lld ]}
            '';
            meta = {
              description = "The Gabbro compiler and checker";
              mainProgram = "gabbro";
            };
          };
        in
        {
          inherit gabbro;
          default = gabbro;
        });

      devShells = forAll (pkgs:
        let llvm = pkgs.llvmPackages_latest; in
        {
          default = pkgs.mkShell {
            packages = [
              pkgs.cargo
              pkgs.rustc
              pkgs.clippy
              pkgs.rustfmt
              pkgs.elan
              llvm.llvm
              llvm.lld
              pkgs.qemu-user
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
