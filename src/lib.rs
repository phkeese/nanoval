/// A NaN-tagged value supporting f64, i32, u32, booleans, null and arbitrary pointers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Value {
    bits: u64,
}

#[repr(u64)]
enum Tag {
    Null = 0 << 48,
    False = 1 << 48,
    True = 2 << 48,
    I32 = 3 << 48,
    U32 = 4 << 48,
}


impl Value {
    /// Sign bit, used to distinguish between pointers and other values.
    const SIGN_BIT: u64 = 1 << 63;
    /// Special NaN value for representing NaNs and non-f64 values.
    const NAN: u64 = 0x7ff8_0000_0000_0000;
    /// Bits set for pointers.
    const POINTER_BITS: u64 = Self::SIGN_BIT | Self::NAN;

    /// Mask used for tag bits. Just 3 bits, shifted to the left by 48 to stay clear of pointer bits.
    const TAG_MASK: u64 = 0b111 << 48;

    /// Constants for faster comparison with booleans and null.
    const FALSE: Self = Self::new_primitive(Tag::False);
    const TRUE: Self = Self::new_primitive(Tag::True);
    const NULL: Self = Self::new_primitive(Tag::Null);

    /// Create a primitive tagged value.
    const fn new_primitive(tag: Tag) -> Self {
        Self { bits: tag as u64 | Self::NAN }
    }

    /// Create a tagged value with a value.
    const fn new(tag: Tag, value: u64) -> Self {
        Self { bits: tag as u64 | Self::NAN | value }
    }

    /// Get tag bits.
    fn tag(self) -> u64 {
        self.bits & Self::TAG_MASK
    }

    /// Is this value a f64?
    /// Valid f64 are not NaN, or if they are, they have a specific bit pattern.
    pub fn is_double(self) -> bool {
        (self.bits & Self::NAN) != Self::NAN
    }

    /// Is this value an i32?
    pub fn is_i32(self) -> bool {
        self.tag() == Tag::I32 as u64
    }

    /// Is this value an u32?
    pub fn is_u32(self) -> bool {
        self.tag() == Tag::U32 as u64
    }

    /// Is this value a boolean?
    pub fn is_bool(self) -> bool {
        self == Self::FALSE || self == Self::TRUE
    }

    /// Is this value a pointer?
    pub fn is_pointer(self) -> bool {
        (self.bits & Self::POINTER_BITS) == Self::POINTER_BITS
    }

    /// Is this value null?
    pub fn is_null(self) -> bool {
        self == Self::NULL
    }

    /// Get the value as a f64.
    pub fn as_double(self) -> Option<f64> {
        if self.is_double() {
            Some(f64::from_bits(self.bits))
        } else {
            None
        }
    }

    /// Get the value as an i32.
    pub fn as_i32(self) -> Option<i32> {
        if self.is_i32() {
            Some(self.bits as i32)
        } else {
            None
        }
    }

    /// Get the value as an u32.
    pub fn as_u32(self) -> Option<u32> {
        if self.is_u32() {
            Some(self.bits as u32)
        } else {
            None
        }
    }

    /// Get the value as a boolean.
    pub fn as_bool(self) -> Option<bool> {
        if self == Self::FALSE {
            Some(false)
        } else if self == Self::TRUE {
            Some(true)
        } else {
            None
        }
    }

    /// Get the value as a pointer.
    pub fn as_pointer<T>(self) -> Option<*const T> {
        if self.is_pointer() {
            Some((self.bits & !Self::POINTER_BITS) as *const T)
        } else {
            None
        }
    }

    /// Unchecked conversion to f64.
    /// # Safety
    /// Conversion to f64 is always safe, but might return NaN.
    pub fn as_double_unchecked(self) -> f64 {
        f64::from_bits(self.bits)
    }

    /// Unchecked conversion to i32.
    /// # Safety
    /// The caller must be certain that the value is an i32.
    pub unsafe fn as_i32_unchecked(self) -> i32 {
        let bits = self.bits as u32 as i32;
        bits
    }

    /// Unchecked conversion to u32.
    /// # Safety
    /// The caller must be certain that the value is an u32.
    pub unsafe fn as_u32_unchecked(self) -> u32 {
        self.bits as u32
    }

    /// Unchecked conversion to boolean.
    /// # Safety
    /// The caller must be certain that the value is a boolean.
    pub unsafe fn as_bool_unchecked(self) -> bool {
        self == Self::TRUE
    }

    /// Unchecked conversion to pointer.
    /// # Safety
    /// The caller must be certain that the value is a pointer.
    pub unsafe fn as_pointer_unchecked<T>(self) -> *const T {
        (self.bits & !Self::POINTER_BITS) as *const T
    }
}

impl From<f64> for Value {
    fn from(value: f64) -> Self {
        if value.is_nan() {
            Self { bits: Self::NAN }
        } else {
            Self { bits: value.to_bits() }
        }
    }
}

impl From<i32> for Value {
    fn from(value: i32) -> Self {
        let bits = value as u32 as u64;
        Self::new(Tag::I32, bits)
    }
}

impl From<u32> for Value {
    fn from(value: u32) -> Self {
        Self::new(Tag::U32, value as u64)
    }
}

impl From<bool> for Value {
    fn from(value: bool) -> Self {
        if value {
            Self::TRUE
        } else {
            Self::FALSE
        }
    }
}

impl From<()> for Value {
    fn from(_: ()) -> Self {
        Self::NULL
    }
}

impl<T> From<*const T> for Value {
    fn from(ptr: *const T) -> Self {
        Self { bits: Self::POINTER_BITS | ptr as u64 }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tagged() {
        assert!(Value::FALSE.is_bool());
        assert!(Value::TRUE.is_bool());
        assert!(Value::NULL.is_null());
        assert!(Value::new_primitive(Tag::I32).is_i32());
        assert!(Value::new_primitive(Tag::U32).is_u32());
    }

    #[test]
    fn test_double() {
        let value = Value::from(42.0);
        assert!(value.is_double());
        assert!(!value.is_i32());
        assert!(!value.is_u32());
        assert!(!value.is_bool());
        assert!(!value.is_null());
        assert_eq!(value.as_double(), Some(42.0));
        unsafe { assert_eq!(value.as_double_unchecked(), 42.0); }
    }

    #[test]
    fn test_i32() {
        let value = Value::from(-1234);
        assert!(!value.is_double());
        assert!(value.is_i32());
        assert!(!value.is_u32());
        assert!(!value.is_bool());
        assert!(!value.is_null());
        assert_eq!(value.as_i32(), Some(-1234));
        unsafe { assert_eq!(value.as_i32_unchecked(), -1234); }
    }

    #[test]
    fn test_u32() {
        let value = Value::from(1234u32);
        assert!(!value.is_double());
        assert!(!value.is_i32());
        assert!(value.is_u32());
        assert!(!value.is_bool());
        assert!(!value.is_null());
        assert_eq!(value.as_u32(), Some(1234u32));
        unsafe { assert_eq!(value.as_u32_unchecked(), 1234u32); }
    }

    #[test]
    fn test_bool() {
        let value = Value::from(true);
        assert!(!value.is_double());
        assert!(!value.is_i32());
        assert!(!value.is_u32());
        assert!(value.is_bool());
        assert!(!value.is_null());
        assert_eq!(value.as_bool(), Some(true));
        unsafe { assert_eq!(value.as_bool_unchecked(), true); }
    }

    #[test]
    fn test_null() {
        let value = Value::from(());
        assert!(!value.is_double());
        assert!(!value.is_i32());
        assert!(!value.is_u32());
        assert!(!value.is_bool());
        assert!(value.is_null());
    }

    #[test]
    fn test_pointer() {
        let ptr = 0xdead_beef as *const u8;
        let value = Value::from(ptr);
        assert!(value.is_pointer());
        assert_eq!(value.as_pointer(), Some(ptr));
        unsafe { assert_eq!(value.as_pointer_unchecked(), ptr); }
    }
}