#![feature(adt_const_params)]
#![feature(const_trait_impl)]
#![feature(const_cmp)]
#![feature(const_convert)]
#![feature(const_fn_floating_point_arithmetic)]
#![allow(incomplete_features)]
#![warn(clippy::pedantic)]
//! A library for handling hex coordinates.
//!
//! Massive credit to [Hexagonal Grids from Red Blob Games](https://www.redblobgames.com/grids/hexagons/).
//!
//! <table class="grid-comparison"><thead><tr><th></th><th>Offset</th><th>Doubled</th><th>Axial</
//! th><th>Cube</th></tr></thead><tbody><tr><th>Pointy Rotation</th><td>evenr,
//! oddr</td><td>doublewidth</td><td rowspan="2">axial</td><td
//! rowspan="2">cube</td></tr><tr><th>Flat Rotation</th><td>evenq,
//! oddq</td><td>doubleheight</td></tr><tr><th>Other Rotations</th><td colspan="2">no</td><td
//! colspan="2">yes</td></tr><tr><th>Vector operations
//! (add,&nbsp;subtract,&nbsp;scale)</th><td>no</td><td>yes</td><td>yes</td><td>yes</td></
//! tr><tr><th>Array
//! storage</th><td>rectangular</td><td>no<sup>*</sup></td><td>rhombus<sup>*</sup></td><td>no<sup>*
//! </sup></td></tr><tr><th>Hash storage</th><td colspan="2">any shape</td><td colspan="2">any
//! shape</td></tr><tr><th>Hexagonal
//! symmetry</th><td>no</td><td>no</td><td>no</td><td>yes</td></tr><tr><th>Easy
//! algorithms</th><td>few</td><td>some</td><td>most</td><td>most</td></tr></tbody></table>
//!
//! The article notes:
//! > My recommendation: if you are only going to use non-rotated rectangular maps, consider the
//! > doubled or offset system that matches your map orientation. For maps with Rotation, or
//! > non-rectangularly shaped maps, use axial/cube. Either choose to store the s coordinate (cube),
//! > or calculate it when needed as -q-r (axial).

use std::ops::{Add, Deref, Sub};

/// A wrapper to make a field immutable.
#[derive(Debug, Clone, Copy)]
pub struct Immutable<T>(T);
impl<T> Immutable<T> {
    pub fn new(value: T) -> Self {
        Immutable(value)
    }
}
impl<T> const Deref for Immutable<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// ```text
///   3   2
///    ╲ ╱
/// 4 ──╳── 1
///    ╱ ╲
///   5   6
/// ```
/// ```text
///   +s  -r
///     ╲ ╱
/// -q ──╳── +q
///     ╱ ╲
///   +r  -s
/// ```
#[derive(Debug, Clone, Copy)]
pub enum Direction {
    One = 0,
    Two = 1,
    Three = 2,
    Four = 3,
    Five = 4,
    Six = 6,
}
#[allow(non_upper_case_globals)]
impl Direction {
    pub const QMinus: Self = Self::Four;
    pub const QPlus: Self = Self::One;
    pub const RMinus: Self = Self::Two;
    pub const RPlus: Self = Self::Five;
    pub const SMinus: Self = Self::Six;
    pub const SPlus: Self = Self::Three;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OffsetSystem {
    /// ```text
    ///    ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲
    ///   |0,0|1,0|2,0|3,0|4,0|5,0|6,0|
    ///  ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱
    /// │0,1│1,1│2,1│3,1│4,1│5,1│6,1│
    ///  ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲
    ///   |0,2|1,2|2,2|3,2|4,2|5,2|6,2|
    ///  ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱
    /// │0,3│1,3│2,3│3,3│4,3│5,3│6,3│
    ///  ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲
    ///   |0,4|1,4|2,4|3,4|4,4|5,4|6,4|
    ///    ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱
    /// ```
    OddR,
    /// ```text
    ///  ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲
    /// │0,0│1,0│2,0│3,0│4,0│5,0│6,0│
    ///  ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲
    ///   |0,1|1,1|2,1|3,1|4,1|5,1|6,1|
    ///  ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱
    /// │0,2│1,2│2,2│3,2│4,2│5,2│6,2│
    ///  ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲
    ///   |0,3|1,3|2,3|3,3|4,3|5,3|6,3|
    ///  ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱
    /// │0,4│1,4│2,4│3,4│4,4│5,4│6,4│
    ///  ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱
    /// ```
    EvenR,
    /// ```text
    ///   ___     ___     ___     ___     
    ///  ╱0,0╲___╱2,0╲___╱4,0╲___╱6,0╲___
    ///  ╲___╱1,0╲___╱3,0╲___╱5,0╲___╱7,0╲
    ///  ╱0,1╲___╱2,1╲___╱4,1╲___╱6,1╲___╱
    ///  ╲___╱1,1╲___╱3,1╲___╱5,1╲___╱7,1╲
    ///  ╱0,2╲___╱2,2╲___╱4,2╲___╱6,2╲___╱
    ///  ╲___╱1,2╲___╱3,2╲___╱5,2╲___╱7,2╲
    ///  ╱0,3╲___╱2,3╲___╱4,3╲___╱6,3╲___╱
    ///  ╲___╱1,3╲___╱3,3╲___╱5,3╲___╱7,3╲
    ///  ╱0,4╲___╱2,4╲___╱4,4╲___╱6,4╲___╱
    ///  ╲___╱1,4╲___╱3,4╲___╱5,4╲___╱7,4╲
    ///      ╲___╱   ╲___╱   ╲___╱   ╲___╱
    /// ```
    OddQ,
    /// ```text
    ///       ___     ___     ___     ___
    ///   ___╱1,0╲___╱3,0╲___╱5,0╲___╱7,0╲
    ///  ╱0,0╲___╱2,0╲___╱4,0╲___╱6,0╲___╱
    ///  ╲___╱1,1╲___╱3,1╲___╱5,1╲___╱7,1╲
    ///  ╱0,1╲___╱2,1╲___╱4,1╲___╱6,1╲___╱
    ///  ╲___╱1,2╲___╱3,2╲___╱5,2╲___╱7,2╲
    ///  ╱0,2╲___╱2,2╲___╱4,2╲___╱6,2╲___╱
    ///  ╲___╱1,3╲___╱3,3╲___╱5,3╲___╱7,3╲
    ///  ╱0,3╲___╱2,3╲___╱4,3╲___╱6,3╲___╱
    ///  ╲___╱1,4╲___╱3,4╲___╱5,4╲___╱7,4╲
    ///  ╱0,4╲___╱2,4╲___╱4,4╲___╱6,4╲___╱
    ///  ╲___╱   ╲___╱   ╲___╱   ╲___╱
    /// ```
    EvenQ,
}

/// See [`OffsetSystem`].
#[derive(Debug, Clone, Copy)]
pub struct OffsetCoordinates<const S: OffsetSystem> {
    // Column
    pub col: isize,
    // Row
    pub row: isize,
}
impl<const S: OffsetSystem> OffsetCoordinates<S> {
    /// Constructs new coordinate.
    #[must_use]
    pub const fn new(col: isize, row: isize) -> Self {
        Self { col, row }
    }
}
impl OffsetCoordinates<{ OffsetSystem::OddR }> {
    #[must_use]
    pub const fn neighbor(&self, direction: Direction) -> Self {
        let parity = Row::from(*self);
        *self + Self::from((parity, direction))
    }

    /// Returns the manhattan distance between 2 coordinates.
    #[must_use]
    pub const fn manhattan_distance(&self, other: Self) -> usize {
        let a = AxialCoordinates::from(*self);
        let b = AxialCoordinates::from(other);
        a.manhattan_distance(b)
    }

    /// Returns all coordinates `steps` steps from `self` where `{ -range <= steps <= range }`.
    ///
    /// # Panics
    ///
    /// When `isize::try_from(range).is_err()`.
    #[must_use]
    pub fn coordinate_range(&self, range: usize) -> Vec<Self> {
        let axial = AxialCoordinates::from(*self);
        let axial_range = axial.coordinate_range(range);
        axial_range.into_iter().map(Self::from).collect()
    }

    /// Returns coordinates resulting from rotating `self` about `center` by `Rotation`.
    #[must_use]
    pub const fn rotate(&self, center: Self, rotation: Rotation) -> Self {
        let axial_self = AxialCoordinates::from(*self);
        let axial_center = AxialCoordinates::from(center);
        axial_self.rotate(axial_center, rotation).into()
    }
}
impl OffsetCoordinates<{ OffsetSystem::EvenR }> {
    #[must_use]
    pub const fn neighbor(&self, direction: Direction) -> Self {
        let parity = Row::from(*self);
        *self + Self::from((parity, direction))
    }

    /// Returns the manhattan distance between 2 coordinates.
    #[must_use]
    pub const fn manhattan_distance(&self, other: Self) -> usize {
        let a = AxialCoordinates::from(*self);
        let b = AxialCoordinates::from(other);
        a.manhattan_distance(b)
    }

    /// Returns all coordinates `steps` steps from `self` where `{ -range <= steps <= range }`.
    ///
    /// # Panics
    ///
    /// When `isize::try_from(range).is_err()`.
    #[must_use]
    pub fn coordinate_range(&self, range: usize) -> Vec<Self> {
        let axial = AxialCoordinates::from(*self);
        let axial_range = axial.coordinate_range(range);
        axial_range.into_iter().map(Self::from).collect()
    }

    /// Returns coordinates resulting from rotating `self` about `center` by `Rotation`.
    #[must_use]
    pub const fn rotate(&self, center: Self, rotation: Rotation) -> Self {
        let axial_self = AxialCoordinates::from(*self);
        let axial_center = AxialCoordinates::from(center);
        axial_self.rotate(axial_center, rotation).into()
    }
}
impl OffsetCoordinates<{ OffsetSystem::OddQ }> {
    #[must_use]
    pub const fn neighbor(&self, direction: Direction) -> Self {
        let parity = Col::from(*self);
        *self + Self::from((parity, direction))
    }

    /// Returns the manhattan distance between 2 coordinates.
    #[must_use]
    pub const fn manhattan_distance(&self, other: Self) -> usize {
        let a = AxialCoordinates::from(*self);
        let b = AxialCoordinates::from(other);
        a.manhattan_distance(b)
    }

    /// Returns all coordinates `steps` steps from `self` where `{ -range <= steps <= range }`.
    ///
    /// # Panics
    ///
    /// When `isize::try_from(range).is_err()`.
    #[must_use]
    pub fn coordinate_range(&self, range: usize) -> Vec<Self> {
        let axial = AxialCoordinates::from(*self);
        let axial_range = axial.coordinate_range(range);
        axial_range.into_iter().map(Self::from).collect()
    }

    /// Returns coordinates resulting from rotating `self` about `center` by `Rotation`.
    #[must_use]
    pub const fn rotate(&self, center: Self, rotation: Rotation) -> Self {
        let axial_self = AxialCoordinates::from(*self);
        let axial_center = AxialCoordinates::from(center);
        axial_self.rotate(axial_center, rotation).into()
    }
}
impl OffsetCoordinates<{ OffsetSystem::EvenQ }> {
    #[must_use]
    pub const fn neighbor(&self, direction: Direction) -> Self {
        let parity = Col::from(*self);
        *self + Self::from((parity, direction))
    }

    /// Returns the manhattan distance between 2 coordinates.
    #[must_use]
    pub const fn manhattan_distance(&self, other: Self) -> usize {
        let a = AxialCoordinates::from(*self);
        let b = AxialCoordinates::from(other);
        a.manhattan_distance(b)
    }

    /// Returns all coordinates `steps` steps from `self` where `{ -range <= steps <= range }`.
    ///
    /// # Panics
    ///
    /// When `isize::try_from(range).is_err()`.
    #[must_use]
    pub fn coordinate_range(&self, range: usize) -> Vec<Self> {
        let axial = AxialCoordinates::from(*self);
        let axial_range = axial.coordinate_range(range);
        axial_range.into_iter().map(Self::from).collect()
    }

    /// Returns coordinates resulting from rotating `self` about `center` by `Rotation`.
    #[must_use]
    pub const fn rotate(&self, center: Self, rotation: Rotation) -> Self {
        let axial_self = AxialCoordinates::from(*self);
        let axial_center = AxialCoordinates::from(center);
        axial_self.rotate(axial_center, rotation).into()
    }
}
impl const From<AxialCoordinates> for OffsetCoordinates<{ OffsetSystem::OddR }> {
    fn from(AxialCoordinates { q, r }: AxialCoordinates) -> Self {
        let col = q + (r - (r & 1)) / 2;
        let row = r;
        Self { col, row }
    }
}
impl const From<AxialCoordinates> for OffsetCoordinates<{ OffsetSystem::EvenR }> {
    fn from(AxialCoordinates { q, r }: AxialCoordinates) -> Self {
        let col = q + (r + (r & 1)) / 2;
        let row = r;
        Self { col, row }
    }
}
impl const From<AxialCoordinates> for OffsetCoordinates<{ OffsetSystem::OddQ }> {
    fn from(AxialCoordinates { q, r }: AxialCoordinates) -> Self {
        let col = q;
        let row = r + (q - (q & 1)) / 2;
        Self { col, row }
    }
}
impl const From<AxialCoordinates> for OffsetCoordinates<{ OffsetSystem::EvenQ }> {
    fn from(AxialCoordinates { q, r }: AxialCoordinates) -> Self {
        let col = q;
        let row = r + (q + (q & 1)) / 2;
        Self { col, row }
    }
}

/// This is arguably excessively explicit, but I want to specify when passing this parameter it
/// relates to the rows being even or odd.
pub enum Row {
    Even,
    Odd,
}
impl<const S: OffsetSystem> const From<OffsetCoordinates<S>> for Row {
    fn from(OffsetCoordinates { row, .. }: OffsetCoordinates<S>) -> Self {
        if row & 1 == 0 {
            Self::Even
        } else {
            Self::Odd
        }
    }
}
/// This is arguably excessively explicit, but I want to specify when passing this parameter it
/// relates to the columns being even or odd.
pub enum Col {
    Even,
    Odd,
}
impl<const S: OffsetSystem> const From<OffsetCoordinates<S>> for Col {
    fn from(OffsetCoordinates { col, .. }: OffsetCoordinates<S>) -> Self {
        if col & 1 == 0 {
            Self::Even
        } else {
            Self::Odd
        }
    }
}

impl const From<(Row, Direction)> for OffsetCoordinates<{ OffsetSystem::OddR }> {
    fn from((row, direction): (Row, Direction)) -> Self {
        match row {
            Row::Even => match direction {
                Direction::One => Self { col: 1, row: 0 },
                Direction::Two => Self { col: 0, row: -1 },
                Direction::Three => Self { col: -1, row: -1 },
                Direction::Four => Self { col: -1, row: 0 },
                Direction::Five => Self { col: -1, row: 1 },
                Direction::Six => Self { col: 0, row: 1 },
            },
            Row::Odd => match direction {
                Direction::One => Self { col: 1, row: 0 },
                Direction::Two => Self { col: 1, row: -1 },
                Direction::Three => Self { col: 0, row: -1 },
                Direction::Four => Self { col: -1, row: 0 },
                Direction::Five => Self { col: 0, row: 1 },
                Direction::Six => Self { col: 1, row: 1 },
            },
        }
    }
}
impl const From<(Row, Direction)> for OffsetCoordinates<{ OffsetSystem::EvenR }> {
    fn from((row, direction): (Row, Direction)) -> Self {
        match row {
            Row::Odd => match direction {
                Direction::One => Self { col: 1, row: 0 },
                Direction::Two => Self { col: 0, row: -1 },
                Direction::Three => Self { col: -1, row: -1 },
                Direction::Four => Self { col: -1, row: 0 },
                Direction::Five => Self { col: -1, row: 1 },
                Direction::Six => Self { col: 0, row: 1 },
            },
            Row::Even => match direction {
                Direction::One => Self { col: 1, row: 0 },
                Direction::Two => Self { col: 1, row: -1 },
                Direction::Three => Self { col: 0, row: -1 },
                Direction::Four => Self { col: -1, row: 0 },
                Direction::Five => Self { col: 0, row: 1 },
                Direction::Six => Self { col: 1, row: 1 },
            },
        }
    }
}
impl const From<(Col, Direction)> for OffsetCoordinates<{ OffsetSystem::OddQ }> {
    fn from((col, direction): (Col, Direction)) -> Self {
        match col {
            Col::Even => match direction {
                Direction::One => Self { col: 1, row: 0 },
                Direction::Two => Self { col: 1, row: -1 },
                Direction::Three => Self { col: 0, row: -1 },
                Direction::Four => Self { col: -1, row: -1 },
                Direction::Five => Self { col: -1, row: 0 },
                Direction::Six => Self { col: 0, row: 1 },
            },
            Col::Odd => match direction {
                Direction::One => Self { col: 1, row: 1 },
                Direction::Two => Self { col: 1, row: 0 },
                Direction::Three => Self { col: 0, row: -1 },
                Direction::Four => Self { col: -1, row: 0 },
                Direction::Five => Self { col: -1, row: 1 },
                Direction::Six => Self { col: 0, row: 1 },
            },
        }
    }
}
impl const From<(Col, Direction)> for OffsetCoordinates<{ OffsetSystem::EvenQ }> {
    fn from((col, direction): (Col, Direction)) -> Self {
        match col {
            Col::Odd => match direction {
                Direction::One => Self { col: 1, row: 0 },
                Direction::Two => Self { col: 1, row: -1 },
                Direction::Three => Self { col: 0, row: -1 },
                Direction::Four => Self { col: -1, row: -1 },
                Direction::Five => Self { col: -1, row: 0 },
                Direction::Six => Self { col: 0, row: 1 },
            },
            Col::Even => match direction {
                Direction::One => Self { col: 1, row: 1 },
                Direction::Two => Self { col: 1, row: 0 },
                Direction::Three => Self { col: 0, row: -1 },
                Direction::Four => Self { col: -1, row: 0 },
                Direction::Five => Self { col: -1, row: 1 },
                Direction::Six => Self { col: 0, row: 1 },
            },
        }
    }
}
impl<const S: OffsetSystem> const Add for OffsetCoordinates<S> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Self {
            col: self.col + other.col,
            row: self.row + other.row,
        }
    }
}
impl<const S: OffsetSystem> const Sub for OffsetCoordinates<S> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        Self {
            col: self.col - other.col,
            row: self.row - other.row,
        }
    }
}

/// A clockwise Rotation
#[derive(Debug, Clone, Copy)]
pub enum Rotation {
    /// 360°, 2π, -360°, -2π
    Zero = 0,
    /// -300°, -⁵⁄₃π
    One = 1,
    /// -240°, -⁴⁄₃π
    Two = 2,
    /// -180°, -π
    Three = 3,
    /// -120°, -⅔π
    Four = 4,
    /// -60°, -⅓π
    Five = 5,
    /// 0°, 0
    Six = 6,
    /// 60°, ⅓π
    Seven = 7,
    /// 120°, ⅔π
    Eight = 8,
    /// 180°, π
    Nine = 9,
    /// 240°, ⁴⁄₃π
    Ten = 10,
    /// 300°, ⁵⁄₃π
    Eleven = 11,
}

impl const Add for Rotation {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        let v = (self as u8 + other as u8) % 12;
        Self::from(v)
    }
}
impl const Sub for Rotation {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        let v = (self as u8 - other as u8) % 12;
        Self::from(v)
    }
}
impl const From<u8> for Rotation {
    /// Inverse of `Rotation as u8`
    fn from(x: u8) -> Self {
        match x {
            0 => Self::Zero,
            1 => Self::One,
            2 => Self::Two,
            3 => Self::Three,
            4 => Self::Four,
            5 => Self::Five,
            6 => Self::Six,
            7 => Self::Seven,
            8 => Self::Eight,
            9 => Self::Nine,
            10 => Self::Ten,
            11 => Self::Eleven,
            _ => unreachable!(),
        }
    }
}
impl const TryFrom<i16> for Rotation {
    type Error = ();

    /// Constructs `Self` from `int` degrees.
    ///
    /// # Errors
    ///
    /// When `int` does not equal 0°, 60°, 120°, 180°, 240°, 300° or 360° (or their negatives).
    fn try_from(int: i16) -> Result<Self, Self::Error> {
        match int {
            -360 | 360 => Ok(Self::Zero),
            -300 => Ok(Self::One),
            -240 => Ok(Self::Two),
            -180 => Ok(Self::Three),
            -120 => Ok(Self::Four),
            -60 => Ok(Self::Five),
            0 => Ok(Self::Six),
            60 => Ok(Self::Seven),
            120 => Ok(Self::Eight),
            180 => Ok(Self::Nine),
            240 => Ok(Self::Ten),
            300 => Ok(Self::Eleven),
            _ => Err(()),
        }
    }
}
impl const TryFrom<f32> for Rotation {
    type Error = ();

    /// Constructs `Self` from `float` radians.
    ///
    /// # Errors
    ///
    /// When `float` does not equal 0, ⅓π, ⅔π, π, ⁴⁄₃π, ⁵⁄₃π or 2π (or their negatives).
    fn try_from(float: f32) -> Result<Self, Self::Error> {
        use std::f32::consts::PI;
        const P1: f32 = (1. / 3.) * PI;
        const P2: f32 = (2. / 3.) * PI;
        const P3: f32 = PI;
        const P4: f32 = (4. / 3.) * PI;
        const P5: f32 = (5. / 3.) * PI;
        const P6: f32 = (6. / 3.) * PI;
        const NP1: f32 = -P1;
        const NP2: f32 = -P2;
        const NP3: f32 = -P3;
        const NP4: f32 = -P4;
        const NP5: f32 = -P5;
        const NP6: f32 = -P6;

        match float {
            x if x == NP6 || x == P6 => Ok(Self::Zero),
            x if x == NP5 => Ok(Self::One),
            x if x == NP4 => Ok(Self::Two),
            x if x == NP3 => Ok(Self::Three),
            x if x == NP2 => Ok(Self::Four),
            x if x == NP1 => Ok(Self::Five),
            x if x == 0. => Ok(Self::Six),
            x if x == P1 => Ok(Self::Seven),
            x if x == P2 => Ok(Self::Eight),
            x if x == P3 => Ok(Self::Nine),
            x if x == P4 => Ok(Self::Ten),
            x if x == P5 => Ok(Self::Eleven),
            _ => Err(()),
        }
    }
}

/// ```text
///  _____
/// ╱ r, s╲
/// ╲__q__╱
/// ```
/// ```text
///         _____
///   _____╱+1,-1╲_____
///  ╱ 0,+1╲__0__╱-1, 0╲
///  ╲_-1__╱ 0, 0╲_+1__╱
///  ╱+1, 0╲__0__╱ 0,-1╲
///  ╲_-1__╱+1,-1╲_+1__╱
///        ╲__0__╱
/// ```
/// ```text
///   +s  -r
///     ╲ ╱
/// -q ──╳── +q
///     ╱ ╲
///   +r  -s
/// ```
#[derive(Debug, Clone, Copy)]
pub struct CubeCoordinates {
    pub q: Immutable<isize>,
    pub r: Immutable<isize>,
    pub s: Immutable<isize>,
}
impl CubeCoordinates {
    /// Constructs new coordinate.
    ///
    /// # Errors
    ///
    /// When `q + r + s != 0`.
    pub const fn new(q: isize, r: isize, s: isize) -> Result<Self, &'static str> {
        if q + r + s == 0 {
            Ok(Self {
                q: Immutable(q),
                r: Immutable(r),
                s: Immutable(s),
            })
        } else {
            Err("q + r + s != 0")
        }
    }

    /// Returns the neighboring coordinates in a given direction.
    #[must_use]
    pub const fn neighbor(&self, direction: Direction) -> Self {
        *self + Self::from(direction)
    }

    /// Returns the manhattan distance between 2 coordinates.
    #[must_use]
    pub const fn manhattan_distance(&self, other: Self) -> usize {
        (((*self.q - *other.q).abs() + (*self.r - *other.r).abs() + (*self.s - *other.s).abs()) / 2)
            as usize
    }

    /// Returns all coordinates `steps` steps from `self` where `{ -range <= steps <= range }`.
    ///
    /// # Panics
    ///
    /// When `isize::try_from(range).is_err()`.
    #[must_use]
    pub fn coordinate_range(&self, range: usize) -> Vec<Self> {
        let range = isize::try_from(range).unwrap();
        let mut results = Vec::new();
        for q in -range..=range {
            for r in std::cmp::max(-range, -q - range)..=std::cmp::min(range, -q + range) {
                let s = -q - r;
                results.push(
                    *self
                        + Self {
                            q: Immutable(q),
                            r: Immutable(r),
                            s: Immutable(s),
                        },
                );
            }
        }
        results
    }

    /// Returns coordinates resulting from rotating `self` about `center` by `Rotation`.
    #[must_use]
    pub const fn rotate(&self, center: Self, rotation: Rotation) -> Self {
        let vec = *self - center;
        let rotated = match rotation {
            Rotation::Zero | Rotation::Six => vec,
            Rotation::One | Rotation::Eleven => Self {
                q: Immutable(-*vec.r),
                r: Immutable(-*vec.s),
                s: Immutable(-*vec.q),
            },
            Rotation::Two | Rotation::Ten => Self {
                q: Immutable(*vec.s),
                r: Immutable(*vec.q),
                s: Immutable(*vec.r),
            },
            Rotation::Three | Rotation::Nine => Self {
                q: Immutable(-*vec.q),
                r: Immutable(-*vec.r),
                s: Immutable(-*vec.s),
            },
            Rotation::Four | Rotation::Eight => Self {
                q: Immutable(*vec.r),
                r: Immutable(*vec.s),
                s: Immutable(*vec.q),
            },
            Rotation::Five | Rotation::Seven => Self {
                q: Immutable(-*vec.s),
                r: Immutable(-*vec.q),
                s: Immutable(-*vec.r),
            },
        };
        rotated + center
    }
}
impl const From<AxialCoordinates> for CubeCoordinates {
    fn from(AxialCoordinates { q, r }: AxialCoordinates) -> Self {
        Self {
            q: Immutable(q),
            r: Immutable(r),
            s: Immutable(-q - r),
        }
    }
}
impl const From<Direction> for CubeCoordinates {
    fn from(direction: Direction) -> Self {
        match direction {
            Direction::One => Self {
                q: Immutable(1),
                r: Immutable(0),
                s: Immutable(-1),
            },
            Direction::Two => Self {
                q: Immutable(1),
                r: Immutable(-1),
                s: Immutable(0),
            },
            Direction::Three => Self {
                q: Immutable(0),
                r: Immutable(-1),
                s: Immutable(1),
            },
            Direction::Four => Self {
                q: Immutable(-1),
                r: Immutable(0),
                s: Immutable(1),
            },
            Direction::Five => Self {
                q: Immutable(-1),
                r: Immutable(1),
                s: Immutable(0),
            },
            Direction::Six => Self {
                q: Immutable(0),
                r: Immutable(1),
                s: Immutable(-1),
            },
        }
    }
}
impl const Add for CubeCoordinates {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Self {
            q: Immutable(*self.q + *other.q),
            r: Immutable(*self.r + *other.r),
            s: Immutable(*self.s + *other.s),
        }
    }
}
impl const Sub for CubeCoordinates {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        Self {
            q: Immutable(*self.q - *other.q),
            r: Immutable(*self.r - *other.r),
            s: Immutable(*self.s - *other.s),
        }
    }
}

/// [`CubeCoordinates`] minus `s` coordinate.
#[derive(Debug, Clone, Copy)]
pub struct AxialCoordinates {
    pub q: isize,
    pub r: isize,
}
impl AxialCoordinates {
    /// Constructs new coordinate.
    #[must_use]
    pub const fn new(q: isize, r: isize) -> Self {
        Self { q, r }
    }

    /// Calculate the `s` coordinate
    #[must_use]
    pub const fn s(&self) -> isize {
        -self.q - self.r
    }

    /// Returns the neighboring coordinates in a given direction.
    #[must_use]
    pub const fn neighbor(&self, direction: Direction) -> Self {
        *self + Self::from(direction)
    }

    /// Returns the manhattan distance between 2 coordinates.
    #[must_use]
    pub const fn manhattan_distance(&self, other: Self) -> usize {
        (((self.q - other.q).abs()
            + (self.r - other.r).abs()
            + (self.q + self.r - other.q - other.r).abs())
            / 2) as usize
        // Akin to:
        // let a = CubeCoordinates::from(*self);
        // let b = CubeCoordinates::from(other);
        // a.manhattan_distance(b)
    }

    /// Returns all coordinates `steps` steps from `self` where `{ -range <= steps <= range }`.
    ///
    /// # Panics
    ///
    /// When `isize::try_from(range).is_err()`.
    #[must_use]
    pub fn coordinate_range(&self, range: usize) -> Vec<Self> {
        let range = isize::try_from(range).unwrap();
        let mut results = Vec::new();
        for q in -range..=range {
            for r in std::cmp::max(-range, -q - range)..=std::cmp::min(range, -q + range) {
                results.push(*self + Self { q, r });
            }
        }
        results
    }

    /// Returns coordinates resulting from rotating `self` about `center` by `Rotation`.
    #[must_use]
    pub const fn rotate(&self, center: Self, rotation: Rotation) -> Self {
        let vec = *self - center;
        let rotated = match rotation {
            Rotation::Zero | Rotation::Six => vec,
            Rotation::One | Rotation::Eleven => Self {
                q: -vec.r,
                r: -vec.s(),
            },
            Rotation::Two | Rotation::Ten => Self {
                q: vec.s(),
                r: vec.q,
            },
            Rotation::Three | Rotation::Nine => Self {
                q: -vec.q,
                r: -vec.r,
            },
            Rotation::Four | Rotation::Eight => Self {
                q: vec.r,
                r: vec.s(),
            },
            Rotation::Five | Rotation::Seven => Self {
                q: -vec.s(),
                r: -vec.q,
            },
        };
        rotated + center
    }
}
impl const From<CubeCoordinates> for AxialCoordinates {
    fn from(CubeCoordinates { q, r, s: _ }: CubeCoordinates) -> Self {
        Self { q: *q, r: *r }
    }
}
impl const From<OffsetCoordinates<{ OffsetSystem::OddR }>> for AxialCoordinates {
    fn from(OffsetCoordinates { col, row }: OffsetCoordinates<{ OffsetSystem::OddR }>) -> Self {
        let q = col - (row - (row & 1)) / 2;
        let r = row;
        Self { q, r }
    }
}
impl const From<OffsetCoordinates<{ OffsetSystem::EvenR }>> for AxialCoordinates {
    fn from(OffsetCoordinates { col, row }: OffsetCoordinates<{ OffsetSystem::EvenR }>) -> Self {
        let q = col - (row + (row & 1)) / 2;
        let r = row;
        Self { q, r }
    }
}
impl const From<OffsetCoordinates<{ OffsetSystem::OddQ }>> for AxialCoordinates {
    fn from(OffsetCoordinates { col, row }: OffsetCoordinates<{ OffsetSystem::OddQ }>) -> Self {
        let q = col;
        let r = row - (col - (col & 1)) / 2;
        Self { q, r }
    }
}
impl const From<OffsetCoordinates<{ OffsetSystem::EvenQ }>> for AxialCoordinates {
    fn from(OffsetCoordinates { col, row }: OffsetCoordinates<{ OffsetSystem::EvenQ }>) -> Self {
        let q = col;
        let r = row - (col + (col & 1)) / 2;
        Self { q, r }
    }
}
impl const From<DoubledCoordinates<{ DoubledSystem::Height }>> for AxialCoordinates {
    fn from(
        DoubledCoordinates { col, row }: DoubledCoordinates<{ DoubledSystem::Height }>,
    ) -> Self {
        let q = *col;
        let r = (*row - *col) / 2;
        Self { q, r }
    }
}
impl const From<DoubledCoordinates<{ DoubledSystem::Width }>> for AxialCoordinates {
    fn from(DoubledCoordinates { col, row }: DoubledCoordinates<{ DoubledSystem::Width }>) -> Self {
        let q = (*col - *row) / 2;
        let r = *row;
        Self { q, r }
    }
}
impl const From<Direction> for AxialCoordinates {
    fn from(direction: Direction) -> Self {
        match direction {
            Direction::One => Self { q: 1, r: 0 },
            Direction::Two => Self { q: 1, r: -1 },
            Direction::Three => Self { q: 0, r: -1 },
            Direction::Four => Self { q: -1, r: 0 },
            Direction::Five => Self { q: -1, r: 1 },
            Direction::Six => Self { q: 0, r: 1 },
        }
    }
}
impl const Add for AxialCoordinates {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Self {
            q: self.q + other.q,
            r: self.r + other.r,
        }
    }
}
impl const Sub for AxialCoordinates {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        Self {
            q: self.q - other.q,
            r: self.r - other.r,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DoubledSystem {
    /// ```text
    ///  ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲
    /// │0,0│2,0│4,0│6,0│8,0│
    ///  ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲
    ///   |1,1|3,1|5,1|7,1|9,1|
    ///  ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱
    /// │0,2│2,2│4,2│6,2│8,2│
    ///  ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲
    ///   |1,3|3,3|5,3|7,3|9,3|
    ///  ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱
    /// │0,4│2,4│4,4│6,4│8,4│
    ///  ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱ ╲ ╱
    /// ```
    Width,
    /// ```text
    ///   ___     ___     ___     ___     
    ///  ╱0,0╲___╱2,0╲___╱4,0╲___╱6,0╲___
    ///  ╲___╱1,1╲___╱3,1╲___╱5,1╲___╱7,1╲
    ///  ╱0,2╲___╱2,2╲___╱4,2╲___╱6,2╲___╱
    ///  ╲___╱1,3╲___╱3,3╲___╱5,3╲___╱7,3╲
    ///  ╱0,4╲___╱2,4╲___╱4,4╲___╱6,4╲___╱
    ///  ╲___╱1,5╲___╱3,5╲___╱5,5╲___╱7,5╲
    ///  ╱0,6╲___╱2,6╲___╱4,6╲___╱6,6╲___╱
    ///  ╲___╱1,7╲___╱3,7╲___╱5,7╲___╱7,7╲
    ///  ╱0,8╲___╱2,8╲___╱4,8╲___╱6,8╲___╱
    ///  ╲___╱1,9╲___╱3,9╲___╱5,9╲___╱7,9╲
    ///      ╲___╱   ╲___╱   ╲___╱   ╲___╱
    /// ```
    Height,
}
/// See [`DoubledSystem`].
#[derive(Debug, Clone, Copy)]
pub struct DoubledCoordinates<const S: DoubledSystem> {
    // Column
    pub col: Immutable<isize>,
    // Row
    pub row: Immutable<isize>,
}
impl<const S: DoubledSystem> DoubledCoordinates<S> {
    /// Constructs new coordinate.
    ///
    /// # Errors
    ///
    /// When `(col + row) % 2 != 0`.
    pub const fn new(col: isize, row: isize) -> Result<Self, &'static str> {
        if (col + row) % 2 == 0 {
            Ok(Self {
                col: Immutable(col),
                row: Immutable(row),
            })
        } else {
            Err("(q + r) % 2 != 0")
        }
    }
}
impl DoubledCoordinates<{ DoubledSystem::Height }> {
    /// Returns the neighboring coordinates in a given direction.
    #[must_use]
    pub const fn neighbor(&self, direction: Direction) -> Self {
        *self + Self::from(direction)
    }

    /// Returns the manhattan distance between 2 coordinates.
    #[must_use]
    pub const fn manhattan_distance(&self, other: Self) -> usize {
        let dcol = (*self.col - *other.col).abs();
        let drow = (*self.row - *other.row).abs();
        (drow + std::cmp::max(0, (dcol - drow) / 2)) as usize
    }

    /// Returns all coordinates `steps` steps from `self` where `{ -range <= steps <= range }`.
    ///
    /// # Panics
    ///
    /// When `isize::try_from(range).is_err()`.
    #[must_use]
    pub fn coordinate_range(&self, range: usize) -> Vec<Self> {
        let axial = AxialCoordinates::from(*self);
        let axial_range = axial.coordinate_range(range);
        axial_range.into_iter().map(Self::from).collect()
    }

    /// Returns coordinates resulting from rotating `self` about `center` by `Rotation`.
    #[must_use]
    pub const fn rotate(&self, center: Self, rotation: Rotation) -> Self {
        let axial_self = AxialCoordinates::from(*self);
        let axial_center = AxialCoordinates::from(center);
        axial_self.rotate(axial_center, rotation).into()
    }
}
impl DoubledCoordinates<{ DoubledSystem::Width }> {
    /// Returns the neighboring coordinates in a given direction.
    #[must_use]
    pub const fn neighbor(&self, direction: Direction) -> Self {
        *self + Self::from(direction)
    }

    /// Returns the manhattan distance between 2 coordinates.
    #[must_use]
    pub const fn manhattan_distance(&self, other: Self) -> usize {
        let dcol = (*self.col - *other.col).abs();
        let drow = (*self.row - *other.row).abs();
        (dcol + std::cmp::max(0, (drow - dcol) / 2)) as usize
    }

    /// Returns all coordinates `steps` steps from `self` where `{ -range <= steps <= range }`.
    ///
    /// # Panics
    ///
    /// When `isize::try_from(range).is_err()`.
    #[must_use]
    pub fn coordinate_range(&self, range: usize) -> Vec<Self> {
        let axial = AxialCoordinates::from(*self);
        let axial_range = axial.coordinate_range(range);
        axial_range.into_iter().map(Self::from).collect()
    }

    /// Returns coordinates resulting from rotating `self` about `center` by `Rotation`.
    #[must_use]
    pub const fn rotate(&self, center: Self, rotation: Rotation) -> Self {
        let axial_self = AxialCoordinates::from(*self);
        let axial_center = AxialCoordinates::from(center);
        axial_self.rotate(axial_center, rotation).into()
    }
}
impl const From<AxialCoordinates> for DoubledCoordinates<{ DoubledSystem::Height }> {
    fn from(AxialCoordinates { q, r }: AxialCoordinates) -> Self {
        let col = q;
        let row = 2 * r + q;
        Self {
            col: Immutable(col),
            row: Immutable(row),
        }
    }
}
impl const From<AxialCoordinates> for DoubledCoordinates<{ DoubledSystem::Width }> {
    fn from(AxialCoordinates { q, r }: AxialCoordinates) -> Self {
        let col = 2 * q + r;
        let row = r;
        Self {
            col: Immutable(col),
            row: Immutable(row),
        }
    }
}
impl const From<Direction> for DoubledCoordinates<{ DoubledSystem::Height }> {
    fn from(direction: Direction) -> Self {
        match direction {
            Direction::One => Self {
                col: Immutable(1),
                row: Immutable(1),
            },
            Direction::Two => Self {
                col: Immutable(1),
                row: Immutable(-1),
            },
            Direction::Three => Self {
                col: Immutable(0),
                row: Immutable(-2),
            },
            Direction::Four => Self {
                col: Immutable(-1),
                row: Immutable(-1),
            },
            Direction::Five => Self {
                col: Immutable(-1),
                row: Immutable(1),
            },
            Direction::Six => Self {
                col: Immutable(0),
                row: Immutable(2),
            },
        }
    }
}
impl const From<Direction> for DoubledCoordinates<{ DoubledSystem::Width }> {
    fn from(direction: Direction) -> Self {
        match direction {
            Direction::One => Self {
                col: Immutable(2),
                row: Immutable(0),
            },
            Direction::Two => Self {
                col: Immutable(1),
                row: Immutable(-1),
            },
            Direction::Three => Self {
                col: Immutable(-1),
                row: Immutable(-1),
            },
            Direction::Four => Self {
                col: Immutable(-2),
                row: Immutable(0),
            },
            Direction::Five => Self {
                col: Immutable(-1),
                row: Immutable(1),
            },
            Direction::Six => Self {
                col: Immutable(1),
                row: Immutable(1),
            },
        }
    }
}
impl<const S: DoubledSystem> const Add for DoubledCoordinates<S> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Self {
            col: Immutable(*self.col + *other.col),
            row: Immutable(*self.row + *other.row),
        }
    }
}
impl<const S: DoubledSystem> const Sub for DoubledCoordinates<S> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        Self {
            col: Immutable(*self.col - *other.col),
            row: Immutable(*self.row - *other.row),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
}
