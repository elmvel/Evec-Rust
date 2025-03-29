use std::fmt;

pub const SUFFIX_QBE: &str = ".ssa";
pub const SUFFIX_LLVM: &str = ".ll";
pub const SUFFIX_C: &str = ".c";

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Os {
    Linux,
}

impl fmt::Display for Os {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Os::Linux => write!(f, "Linux"),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Arch {
    X86_64,
}

impl fmt::Display for Arch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Arch::X86_64 => write!(f, "x86_64"),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Backend {
    Qbe,
    Llvm,
    C,
}

impl fmt::Display for Backend {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Backend::Qbe => write!(f, "QBE"),
            Backend::Llvm => write!(f, "LLVM"),
            Backend::C => write!(f, "C"),
        }
    }
}

pub struct Target {
    os: Os,
    arch: Arch,
    backend: Backend,
}

impl Default for Target {
    fn default() -> Self {
        Target::from(Os::Linux, Arch::X86_64, Backend::Qbe)
    }
}

impl Target {
    pub fn from(os: Os, arch: Arch, backend: Backend) -> Self {
        Self { os, arch, backend }
    }

    pub fn os(&self) -> Os {
        self.os
    }
    pub fn arch(&self) -> Arch {
        self.arch
    }
    pub fn backend(&self) -> Backend {
        self.backend
    }

    pub fn set_os(&mut self, os: Os) {
        self.os = os
    }
    pub fn set_arch(&mut self, arch: Arch) {
        self.arch = arch
    }
    pub fn set_backend(&mut self, backend: Backend) {
        self.backend = backend
    }

    pub fn can_debug_info(&self) -> bool {
        match self.backend {
            Backend::Qbe => false,
            Backend::Llvm => true,
            Backend::C => true,
        }
    }

    pub fn can_backtrace(&self) -> bool {
        self.can_debug_info()
    }
}
