use std::io::{BufRead, BufReader, Read};

use anyhow::{anyhow, Context, Result};

use crate::{AAFramework, Argument, ArgumentSet, InstanceReader, WarningHandler};

/// A reader for the ICCMA 2023 format.
///
/// This object is used to read an [`AAFramework`] encoded using the ICCMA 2023 input format, as defined on [the competition website](https://iccma2023.github.io/rules.html).
/// The [LabelType](crate::LabelType) of the returned argument frameworks is [usize].
///
/// # Example
///
/// ```
/// # use crustabri::{AAFramework, Iccma23Reader, InstanceReader};
/// fn read_af_from_str(s: &str) -> AAFramework<usize> {
///     let reader = Iccma23Reader::default();
///     reader.read(&mut s.as_bytes()).expect("invalid Aspartix AF")
/// }
/// # read_af_from_str("p af 1");
/// ```
#[derive(Default)]
pub struct Iccma23Reader {
    warning_handlers: Vec<WarningHandler>,
}

impl InstanceReader<usize> for Iccma23Reader {
    fn read(&self, reader: &mut dyn Read) -> Result<AAFramework<usize>> {
        let mut af = None;
        let mut n_args = None;
        let br = BufReader::new(reader);
        let mut empty_lines = false;
        for (i, line) in br.lines().enumerate() {
            let context = || format!("while reading line with index {}", i);
            let l = line.with_context(context)?;
            if l.starts_with('#') {
                continue;
            }
            if l.is_empty() {
                empty_lines = true;
                continue;
            }
            if empty_lines {
                return Err(anyhow!("got content after an empty line")).with_context(context);
            }
            let words = l.split_whitespace().collect::<Vec<&str>>();
            if af.is_none() {
                if words.len() != 3 {
                    return Err(anyhow!(
                        r#"error in preamble; expected 3 words, got {}"#,
                        words.len()
                    ))
                    .with_context(context);
                }
                if words[0] != "p" {
                    return Err(anyhow!(
                        r#"error in first word of preamble; expected "p", got "{}""#,
                        words[0]
                    ))
                    .with_context(context);
                }
                if words[1] != "af" {
                    return Err(anyhow!(
                        r#"error in second word of preamble; expected "af", got "{}""#,
                        words[1]
                    ))
                    .with_context(context);
                }
                n_args = match words[2].parse::<isize>() {
                    Ok(n) if n >= 0 => Some(n as usize),
                    _ => {
                        return Err(anyhow!("error in preamble: invalid number of arguments"))
                            .with_context(context)
                    }
                };
                let argument_set =
                    ArgumentSet::new((1..=n_args.unwrap()).collect::<Vec<usize>>().as_slice());
                af = Some(AAFramework::new(argument_set));
                continue;
            }
            if words.len() != 2 {
                return Err(anyhow!(
                    r#"error in attack; expected 2 words, got {}"#,
                    words.len()
                ))
                .with_context(context);
            }
            let attacker = match words[0].parse::<isize>() {
                Ok(n) if n >= 1 && (n as usize) <= n_args.unwrap() => n as usize,
                _ => {
                    return Err(anyhow!(
                        "error in attack: invalid argument index for attacker"
                    ))
                    .with_context(context)
                }
            };
            let attacked = match words[1].parse::<isize>() {
                Ok(n) if n >= 1 && (n as usize) <= n_args.unwrap() => n as usize,
                _ => {
                    return Err(anyhow!(
                        "error in attack: invalid argument index for attacked"
                    ))
                    .with_context(context)
                }
            };
            af.as_mut()
                .unwrap()
                .new_attack_by_ids(attacker - 1, attacked - 1)
                .unwrap();
        }
        match af {
            Some(a) => Ok(a),
            None => Err(anyhow!("missing preamble")),
        }
    }

    fn read_arg_from_str<'a>(
        &self,
        af: &'a AAFramework<usize>,
        arg: &str,
    ) -> Result<&'a Argument<usize>> {
        match arg.parse::<usize>() {
            Ok(n) if n > 0 && n <= af.n_arguments() => {
                Ok(af.argument_set().get_argument_by_id(n - 1))
            }
            _ => Err(anyhow!("unknown arg: {}", arg)),
        }
    }

    fn add_warning_handler(&mut self, h: WarningHandler) {
        self.warning_handlers.push(h);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ok() {
        let instance = "p af 3\n1 2\n3 3\n";
        let af = Iccma23Reader::default()
            .read(&mut instance.as_bytes())
            .unwrap();
        assert_eq!(3, af.n_arguments());
        assert_eq!(2, af.n_attacks());
        assert!(af.attacks().contains(&(0, 1)));
        assert!(af.attacks().contains(&(2, 2)));
    }

    #[test]
    fn test_ok_missing_last_lf() {
        let instance = "p af 3\n1 2\n3 3";
        let af = Iccma23Reader::default()
            .read(&mut instance.as_bytes())
            .unwrap();
        assert_eq!(3, af.n_arguments());
        assert_eq!(2, af.n_attacks());
        assert!(af.attacks().contains(&(0, 1)));
        assert!(af.attacks().contains(&(2, 2)));
    }

    #[test]
    fn test_ok_empty_lines_at_the_end() {
        let instance = "p af 3\n1 2\n3 3\n\n";
        let af = Iccma23Reader::default()
            .read(&mut instance.as_bytes())
            .unwrap();
        assert_eq!(3, af.n_arguments());
        assert_eq!(2, af.n_attacks());
        assert!(af.attacks().contains(&(0, 1)));
        assert!(af.attacks().contains(&(2, 2)));
    }

    #[test]
    fn test_empty_line_at_the_beginning() {
        let instance = "\np af 3\n1 2\n3 3\n";
        assert!(Iccma23Reader::default()
            .read(&mut instance.as_bytes())
            .is_err());
    }

    #[test]
    fn test_empty_line_in_the_middle() {
        let instance = "p af 3\n\n1 2\n3 3\n";
        assert!(Iccma23Reader::default()
            .read(&mut instance.as_bytes())
            .is_err());
    }

    #[test]
    fn test_comment() {
        let instance = "#foo\np af 3\n1 2\n3 3\n";
        let af = Iccma23Reader::default()
            .read(&mut instance.as_bytes())
            .unwrap();
        assert_eq!(3, af.n_arguments());
        assert_eq!(2, af.n_attacks());
        assert!(af.attacks().contains(&(0, 1)));
        assert!(af.attacks().contains(&(2, 2)));
    }

    #[test]
    fn test_error_in_preamble_word_0() {
        let instance = "foo af 3\n1 2\n3 3\n";
        assert!(Iccma23Reader::default()
            .read(&mut instance.as_bytes())
            .is_err());
    }

    #[test]
    fn test_error_in_preamble_word_1() {
        let instance = "p foo 3\n1 2\n3 3\n";
        assert!(Iccma23Reader::default()
            .read(&mut instance.as_bytes())
            .is_err());
    }

    #[test]
    fn test_error_in_preamble_word_2() {
        let instance = "p af foo\n1 2\n3 3\n";
        assert!(Iccma23Reader::default()
            .read(&mut instance.as_bytes())
            .is_err());
    }

    #[test]
    fn test_error_in_preamble_word_3() {
        let instance = "p af 3 foo\n1 2\n3 3\n";
        assert!(Iccma23Reader::default()
            .read(&mut instance.as_bytes())
            .is_err());
    }

    #[test]
    fn test_error_in_attack_word_0() {
        let instance = "p af 3\n4 2\n3 3\n";
        assert!(Iccma23Reader::default()
            .read(&mut instance.as_bytes())
            .is_err());
    }

    #[test]
    fn test_error_in_attack_word_1() {
        let instance = "p af 3\n1 4\n3 3\n";
        assert!(Iccma23Reader::default()
            .read(&mut instance.as_bytes())
            .is_err());
    }

    #[test]
    fn test_error_in_attack_word_2() {
        let instance = "p af 3\n1 2 4\n3 3\n";
        assert!(Iccma23Reader::default()
            .read(&mut instance.as_bytes())
            .is_err());
    }
}
