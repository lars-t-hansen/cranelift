//! Register allocation.
//!
//! This module contains data structures and algorithms used for register allocation.

pub mod coloring;
pub mod live_value_tracker;
pub mod liveness;
pub mod liverange;
pub mod register_set;
pub mod virtregs;

mod affinity;
mod branch_splitting;
mod coalescing;
mod context;
mod diversion;
mod minimal_alloc;
mod pressure;
mod reload;
mod safepoint;
mod solver;
mod spilling;

pub use self::context::{Context, Mechanism};
pub use self::diversion::RegDiversions;
pub use self::register_set::RegisterSet;
pub use self::safepoint::emit_stackmaps;
