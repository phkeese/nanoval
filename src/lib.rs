use std::fmt::{Display, Formatter};

/// A NaN-tagged value supporting f64, i32, u32, booleans, null and arbitrary pointers.
/// ## Usage
///
/// The `Value` type can be constructed from `f64`, `bool`, `i32`, `u32`, `()` and pointers and references to arbitrary `T`:
///
/// ```rust
/// use nanoval::Value;
///
/// let double = Value::from(3.14);
/// let integer = Value::from(42);
/// let boolean = Value::from(true);
/// let null = Value::from(());
/// let pointee = 42;
/// let pointer = Value::from(&pointee);
/// ```
///
/// The constructed value can be converted back to the original type:
///
/// ```rust
/// # use nanoval::Value;
///
/// # let double = Value::from(3.14);
/// # let integer = Value::from(42);
/// # let boolean = Value::from(true);
/// # let null = Value::from(());
/// # let pointee = 42;
/// # let pointer = Value::from(&pointee);
/// assert_eq!(double.as_f64(), Some(3.14));
/// assert_eq!(integer.as_i32(), Some(42));
/// assert_eq!(boolean.as_bool(), Some(true));
/// assert!(null.is_null());
/// assert_eq!(pointer.as_pointer::<i32>(), Some(&pointee as *const i32));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Value {
    bits: u64,
}

#[repr(u64)]
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum Tag {
    F64 = 0,
    Null,
    False,
    True,
    I32,
    U32,
    Pointer,
}


impl Value {
    /// Sign bit, used to distinguish between pointers and other values.
    const SIGN_BIT: u64 = 1 << 63;
    /// Special NaN value for representing NaNs and non-f64 values.
    const QUIET_NAN: u64 = 0x7ff8_0000_0000_0000;
    /// Bits set for pointers.
    const POINTER_BITS: u64 = Self::SIGN_BIT | Self::QUIET_NAN;

    /// Mask used for tag bits. Just 3 bits, shifted to the left by 48 to stay clear of pointer bits.
    const TAG_MASK: u64 = 0b111 << 48;

    /// Constants for faster comparison with booleans and null.
    const FALSE: Self = Self::new_primitive(Tag::False);
    const TRUE: Self = Self::new_primitive(Tag::True);
    const NULL: Self = Self::new_primitive(Tag::Null);
    const NAN: Self = Self::new_primitive(Tag::F64);

    /// Create a primitive tagged value.
    const fn new_primitive(tag: Tag) -> Self {
        let tag = (tag as u64) << 48;
        Self { bits: tag | Self::QUIET_NAN }
    }

    /// Create a tagged value with a value.
    const fn new(tag: Tag, value: u64) -> Self {
        let tag = (tag as u64) << 48;
        Self { bits: tag | Self::QUIET_NAN | value }
    }

    /// Get type of value.
    const fn tag(self) -> Tag {
        if self.is_f64() {
            return Tag::F64;
        } else if self.is_pointer() {
            return Tag::Pointer;
        }
        let tag = (self.bits & Self::TAG_MASK) >> 48;
        match tag {
            x if x == Tag::Null as u64 => Tag::Null,
            x if x == Tag::False as u64 => Tag::False,
            x if x == Tag::True as u64 => Tag::True,
            x if x == Tag::I32 as u64 => Tag::I32,
            x if x == Tag::U32 as u64 => Tag::U32,
            _ => unreachable!()
        }
    }

    /// Is this value a f64?
    /// Valid f64 are not NaN, or if they are, they have a specific bit pattern.
    pub const fn is_f64(self) -> bool {
        if self.bits == Self::NAN.bits {
            true
        } else {
            (self.bits & Self::QUIET_NAN) != Self::QUIET_NAN
        }
    }

    /// Is this value an i32?
    pub const fn is_i32(self) -> bool {
        match self.tag() {
            Tag::I32 => true,
            _ => false,
        }
    }

    /// Is this value an u32?
    pub const fn is_u32(self) -> bool {
        match self.tag() {
            Tag::U32 => true,
            _ => false,
        }
    }

    /// Is this value a boolean?
    pub const fn is_bool(self) -> bool {
        let bits = self.bits;
        bits == Self::FALSE.bits || bits == Self::TRUE.bits
    }

    /// Is this value a pointer?
    pub const fn is_pointer(self) -> bool {
        (self.bits & Self::POINTER_BITS) == Self::POINTER_BITS
    }

    /// Is this value null?
    pub const fn is_null(self) -> bool {
        self.bits == Self::NULL.bits
    }

    /// Get the value as a f64.
    pub fn as_f64(self) -> Option<f64> {
        if self.is_f64() {
            Some(f64::from_bits(self.bits))
        } else {
            None
        }
    }

    /// Get the value as an i32.
    pub const fn as_i32(self) -> Option<i32> {
        if self.is_i32() {
            Some(self.bits as i32)
        } else {
            None
        }
    }

    /// Get the value as an u32.
    pub const fn as_u32(self) -> Option<u32> {
        if self.is_u32() {
            Some(self.bits as u32)
        } else {
            None
        }
    }

    /// Get the value as a boolean.
    pub const fn as_bool(self) -> Option<bool> {
        match self.tag() {
            Tag::False => Some(false),
            Tag::True => Some(true),
            _ => None,
        }
    }

    /// Get the value as a pointer.
    pub const fn as_pointer<T>(self) -> Option<*const T> {
        if self.is_pointer() {
            Some((self.bits & !Self::POINTER_BITS) as *const T)
        } else {
            None
        }
    }

    /// Unchecked conversion to f64.
    /// # Safety
    /// Conversion to f64 is always safe, but might return NaN.
    pub fn as_f64_unchecked(self) -> f64 {
        f64::from_bits(self.bits)
    }

    /// Unchecked conversion to i32.
    /// # Safety
    /// The caller must be certain that the value is an i32.
    pub const unsafe fn as_i32_unchecked(self) -> i32 {
        self.bits as u32 as i32
    }

    /// Unchecked conversion to u32.
    /// # Safety
    /// The caller must be certain that the value is an u32.
    pub const unsafe fn as_u32_unchecked(self) -> u32 {
        self.bits as u32
    }

    /// Unchecked conversion to boolean.
    /// # Safety
    /// The caller must be certain that the value is a boolean.
    pub const unsafe fn as_bool_unchecked(self) -> bool {
        self.bits == Self::TRUE.bits
    }

    /// Unchecked conversion to pointer.
    /// # Safety
    /// The caller must be certain that the value is a pointer.
    pub const unsafe fn as_pointer_unchecked<T>(self) -> *const T {
        (self.bits & !Self::POINTER_BITS) as *const T
    }

    /// Unchecked conversion to reference.
    /// # Safety
    /// The caller must be certain that the value is a pointer.
    pub const unsafe fn as_ref<'a, T>(self) -> &'a T {
        &*self.as_pointer_unchecked()
    }
}

impl From<f64> for Value {
    fn from(value: f64) -> Self {
        if value.is_nan() {
            Self::NAN
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

impl<T> From<&T> for Value {
    fn from(value: &T) -> Self {
        Self::from(value as *const T)
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        unsafe {
            match self.tag() {
                Tag::F64 => write!(f, "{}", self.as_f64_unchecked()),
                Tag::False => write!(f, "false"),
                Tag::True => write!(f, "true"),
                Tag::Null => write!(f, "null"),
                Tag::I32 => write!(f, "{}", self.as_i32_unchecked()),
                Tag::U32 => write!(f, "{}", self.as_u32_unchecked()),
                _ => write!(f, "{:p}", self.as_pointer_unchecked::<u8>()),
            }
        }
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
    fn test_f64() {
        let value = Value::from(42.0);
        assert!(value.is_f64());
        assert!(!value.is_i32());
        assert!(!value.is_u32());
        assert!(!value.is_bool());
        assert!(!value.is_null());
        assert!(!value.is_pointer());
        assert_eq!(value.as_f64(), Some(42.0));
        assert_eq!(value.as_f64_unchecked(), 42.0);
    }

    #[test]
    fn test_nan() {
        let value = Value::from(f64::NAN);
        assert!(value.is_f64());
        assert!(!value.is_i32());
        assert!(!value.is_u32());
        assert!(!value.is_bool());
        assert!(!value.is_null());
        assert!(!value.is_pointer());
        assert!(value.as_f64().unwrap().is_nan());
        assert!(value.as_f64_unchecked().is_nan());
    }

    #[test]
    fn test_i32() {
        let value = Value::from(-1234);
        assert!(!value.is_f64());
        assert!(value.is_i32());
        assert!(!value.is_u32());
        assert!(!value.is_bool());
        assert!(!value.is_null());
        assert!(!value.is_pointer());
        assert_eq!(value.as_i32(), Some(-1234));
        unsafe { assert_eq!(value.as_i32_unchecked(), -1234); }
    }

    #[test]
    fn test_u32() {
        let value = Value::from(1234u32);
        assert!(!value.is_f64());
        assert!(!value.is_i32());
        assert!(value.is_u32());
        assert!(!value.is_bool());
        assert!(!value.is_null());
        assert!(!value.is_pointer());
        assert_eq!(value.as_u32(), Some(1234u32));
        unsafe { assert_eq!(value.as_u32_unchecked(), 1234u32); }
    }

    #[test]
    fn test_bool() {
        let value = Value::from(true);
        assert!(!value.is_f64());
        assert!(!value.is_i32());
        assert!(!value.is_u32());
        assert!(value.is_bool());
        assert!(!value.is_null());
        assert!(!value.is_pointer());
        assert_eq!(value.as_bool(), Some(true));
        unsafe { assert!(value.as_bool_unchecked()); }
    }

    #[test]
    fn test_null() {
        let value = Value::from(());
        assert!(!value.is_f64());
        assert!(!value.is_i32());
        assert!(!value.is_u32());
        assert!(!value.is_bool());
        assert!(value.is_null());
        assert!(!value.is_pointer());
    }

    #[test]
    fn test_pointer() {
        let ptr = 0xdead_beef as *const u8;
        let value = Value::from(ptr);
        assert!(!value.is_f64());
        assert!(!value.is_i32());
        assert!(!value.is_u32());
        assert!(!value.is_bool());
        assert!(!value.is_null());
        assert!(value.is_pointer());
        assert_eq!(value.as_pointer(), Some(ptr));
        unsafe { assert_eq!(value.as_pointer_unchecked(), ptr); }
    }

    #[test]
    fn test_ref() {
        let pointee = 10;
        let pointer = Value::from(&pointee);
        assert!(!pointer.is_f64());
        assert!(!pointer.is_i32());
        assert!(!pointer.is_u32());
        assert!(!pointer.is_bool());
        assert!(!pointer.is_null());
        assert!(pointer.is_pointer());
        unsafe { assert_eq!(pointer.as_ref::<i32>(), &pointee); }
    }

    #[test]
    fn test_display() {
        let value = Value::from(42.0);
        assert_eq!(format!("{}", value), "42");
        let value = Value::from(-1234);
        assert_eq!(format!("{}", value), "-1234");
        let value = Value::from(1234u32);
        assert_eq!(format!("{}", value), "1234");
        let value = Value::from(true);
        assert_eq!(format!("{}", value), "true");
        let value = Value::from(());
        assert_eq!(format!("{}", value), "null");
        let ptr = 0xdead_beef as *const u8;
        let value = Value::from(ptr);
        assert_eq!(format!("{}", value), format!("{:p}", ptr));
    }
}