use std::ops::{AddAssign, ShlAssign, ShrAssign, SubAssign};

use oxidd::util::IsFloatingPoint;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ShiftCounter {
  counter: u128,
  shifts: i32,
}

impl ShiftCounter {
  fn compact(&mut self) {
    let &mut ShiftCounter { mut counter, mut shifts } = self;
    while counter != 0 && (counter & 0b1) == 0 {
      counter >>= 1;
      shifts += 1;
    }
    self.counter = counter;
    self.shifts = shifts;
  }

  pub fn solutions(&self) -> Option<u128> {
    if self.counter > i128::MAX as u128 {
      None
    } else {
      let mut mask: i128 = i128::MIN;
      let &Self { counter, shifts } = self;
      if shifts > 0 {
        mask >>= shifts;
      } else if shifts < 0 {
        mask <<= -shifts;
      }
      if (counter as i128 & mask) > 0 {
        None
      } else if shifts > 0 {
        Some(counter << shifts)
      } else if shifts < 0 {
        Some(counter >> -shifts)
      } else {
        Some(counter)
      }
    }
  }
}
impl From<u32> for ShiftCounter {
  fn from(value: u32) -> Self {
    let counter = value as u128;
    let shifts = 0;

    let mut result = ShiftCounter { counter, shifts };
    result.compact();
    result
  }
}

impl<'a> AddAssign<&'a Self> for ShiftCounter {
  fn add_assign(&mut self, rhs: &'a Self) {
    if self.shifts > rhs.shifts {
      let shifts = rhs.shifts;
      let shift = self.shifts - rhs.shifts;
      let counter = (self.counter << shift) + rhs.counter;
      self.shifts = shifts;
      self.counter = counter;
    } else if self.shifts < rhs.shifts {
      let shifts = self.shifts;
      let shift = rhs.shifts - self.shifts;
      let counter = self.counter + (rhs.counter << shift);
      self.shifts = shifts;
      self.counter = counter;
    } else {
      self.counter = self.counter + rhs.counter;
    }
    self.compact();
  }
}

impl<'a> SubAssign<&'a Self> for ShiftCounter {
  fn sub_assign(&mut self, rhs: &'a Self) {
    if self.shifts > rhs.shifts {
      let shifts = rhs.shifts;
      let shift = self.shifts - rhs.shifts;
      let counter = (self.counter << shift) - rhs.counter;
      self.shifts = shifts;
      self.counter = counter;
    } else if self.shifts < rhs.shifts {
      let shifts = self.shifts;
      let shift = rhs.shifts - self.shifts;
      let counter = self.counter - (rhs.counter << shift);
      self.shifts = shifts;
      self.counter = counter;
    } else {
      self.counter = self.counter - rhs.counter;
    }
    self.compact();
  }
}
impl ShlAssign<u32> for ShiftCounter {
  fn shl_assign(&mut self, rhs: u32) {
    self.shifts += rhs as i32;
    self.compact();
  }
}

impl ShrAssign<u32> for ShiftCounter {
  fn shr_assign(&mut self, rhs: u32) {
    self.shifts -= rhs as i32;
    self.compact();
  }
}

impl IsFloatingPoint for ShiftCounter {
  const FLOATING_POINT: bool = false;
  const MIN_EXP: i32 = 0;
}
