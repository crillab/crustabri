/// An enum acting like a `Result`, but producing warnings instead of errors.
///
/// As there are no error values, there is always an "ok" value, which can be associated with one or more warnings.
pub enum WarningResult<T, W> {
    Ok(T),
    Warned(T, Vec<W>),
}

impl<T, W> WarningResult<T, W> {
    /// Consumes the warning, returning the corresponding `Ok` value.
    ///
    /// The warnings are passed to the provided callback.
    pub fn consume_warnings<F>(self, f: F) -> T
    where
        F: FnOnce(Vec<W>),
    {
        match self {
            WarningResult::Ok(t) => t,
            WarningResult::Warned(t, w) => {
                f(w);
                t
            } // kcov-ignore
        }
    }

    /// Zips two `WarningResult`.
    ///
    /// The value of the returned `WarningResult` is a couple composed of the two initial value.
    /// The list of warnings is the concatenation of the two initial list of warnings.
    /// If this list is empty, an `Ok` value is returned.
    /// If it contains at least one element, a `Warned` value is returned.
    pub fn zip<U>(self, other: WarningResult<U, W>) -> WarningResult<(T, U), W> {
        match self {
            WarningResult::Ok(t) => match other {
                WarningResult::Ok(u) => WarningResult::Ok((t, u)),
                WarningResult::Warned(u, w) => WarningResult::Warned((t, u), w),
            },
            WarningResult::Warned(t, w1) => match other {
                WarningResult::Ok(u) => WarningResult::Warned((t, u), w1),
                WarningResult::Warned(u, w2) => WarningResult::Warned(
                    (t, u),
                    w1.into_iter().chain(w2.into_iter()).collect::<Vec<W>>(),
                ),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_consume_warnings_ok() {
        let mut consumed = false;
        assert_eq!(
            1,
            WarningResult::Ok(1).consume_warnings(|_v: Vec<String>| consumed = true)
        );
        assert!(!consumed);
    }

    #[test]
    fn test_consume_warnings_warned() {
        let mut consumed = false;
        assert_eq!(
            1,
            WarningResult::Warned(1, vec!["".to_string()]).consume_warnings(|_| consumed = true)
        );
        assert!(consumed);
    }

    #[test]
    fn test_zip_oo() {
        let r1: WarningResult<i32, String> = WarningResult::Ok(1);
        let r2 = WarningResult::Ok(2);
        let z = r1.zip(r2);
        let mut consumed = vec![];
        assert_eq!(
            (1, 2),
            z.consume_warnings(|warnings| warnings.into_iter().for_each(|w| consumed.push(w)))
        );
        assert_eq!(vec![] as Vec<String>, consumed);
    }

    #[test]
    fn test_zip_ow() {
        let r1 = WarningResult::Ok(1);
        let r2 = WarningResult::Warned(2, vec!["w2".to_string()]);
        let z = r1.zip(r2);
        let mut consumed = vec![];
        assert_eq!(
            (1, 2),
            z.consume_warnings(|warnings| warnings.into_iter().for_each(|w| consumed.push(w)))
        );
        assert_eq!(vec!["w2".to_string()], consumed);
    }

    #[test]
    fn test_zip_wo() {
        let r1 = WarningResult::Warned(1, vec!["w1".to_string()]);
        let r2 = WarningResult::Ok(2);
        let z = r1.zip(r2);
        let mut consumed = vec![];
        assert_eq!(
            (1, 2),
            z.consume_warnings(|warnings| warnings.into_iter().for_each(|w| consumed.push(w)))
        );
        assert_eq!(vec!["w1".to_string()], consumed);
    }

    #[test]
    fn test_zip_ww() {
        let r1 = WarningResult::Warned(1, vec!["w1".to_string()]);
        let r2 = WarningResult::Warned(2, vec!["w2".to_string()]);
        let z = r1.zip(r2);
        let mut consumed = vec![];
        assert_eq!(
            (1, 2),
            z.consume_warnings(|warnings| warnings.into_iter().for_each(|w| consumed.push(w)))
        );
        assert_eq!(vec!["w1".to_string(), "w2".to_string()], consumed);
    }
}
