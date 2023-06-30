use super::{InstanceReader, WarningHandler};
use crate::aa::{AAFramework, Argument, ArgumentSet};
use anyhow::{anyhow, Context, Result};
use std::io::{BufRead, BufReader, Read};

/// A reader for the ICCMA 2023 format.
///
/// This object is used to read an [`AAFramework`] encoded using the ICCMA 2023 input format, as defined on [the competition website](https://iccma2023.github.io/rules.html).
/// The [LabelType](crate::aa::LabelType) of the returned argument frameworks is [usize].
///
/// # ICCMA 2023 format
///
/// The following content defines an Argumentation Framework with three arguments (given by the indexes `1`, `2` and `3`) and three attacks (`1` and `2` attack each other and `3` attacks `2`).
///
/// ```text
/// p af 3
/// 1 2
/// 2 1
/// 3 2
/// ```
#[derive(Default)]
pub struct Iccma23Reader {
    warning_handlers: Vec<WarningHandler>,
}

impl InstanceReader<usize> for Iccma23Reader {
    fn read(&self, reader: &mut dyn Read) -> Result<AAFramework<usize>> {
        let br = BufReader::new(reader);
        let mut af = None;
        let mut found_empty_lines = false;
        for (i, line) in br.lines().enumerate() {
            let context = || format!("while reading line with index {}", i);
            let l = line.with_context(context)?;
            if l.starts_with('#') {
                continue;
            }
            if l.is_empty() {
                found_empty_lines = true;
                continue;
            }
            if found_empty_lines {
                return Err(anyhow!("got content after an empty line")).with_context(context);
            }
            let words = l.split_whitespace().collect::<Vec<&str>>();
            if af.is_none() {
                let n_args = read_preamble(&words, "af").with_context(context)?;
                let argument_set =
                    ArgumentSet::new_with_labels((1..=n_args).collect::<Vec<usize>>().as_slice());
                af = Some(AAFramework::new_with_argument_set(argument_set));
                continue;
            }
            if words.len() != 2 {
                return Err(anyhow!(
                    r#"error in attack; expected 2 words, got {}"#,
                    words.len()
                ));
            }
            let n_args = af.as_ref().unwrap().n_arguments();
            let read_arg = |word: &str, arg_type| match word.parse::<isize>() {
                Ok(n) if n >= 1 && (n as usize) <= n_args => Ok(n as usize),
                _ => Err(anyhow!(
                    "error in attack: invalid argument index for {}",
                    arg_type
                )),
            };
            let attacker = read_arg(words[0], "attacker").with_context(context)?;
            let attacked = read_arg(words[1], "attacked").with_context(context)?;
            af.as_mut()
                .unwrap()
                .new_attack_by_ids(attacker - 1, attacked - 1)
                .unwrap();
        }
        if af.is_none() {
            return Err(anyhow!("missing preamble"));
        }
        Ok(af.unwrap())
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

pub(crate) fn read_preamble(words: &[&str], expected_kind: &str) -> Result<usize> {
    if words.len() != 3 {
        return Err(anyhow!(
            r#"error in preamble; expected 3 words, got {}"#,
            words.len()
        ));
    }
    if words[0] != "p" {
        return Err(anyhow!(
            r#"error in first word of preamble; expected "p", got "{}""#,
            words[0]
        ));
    }
    if words[1] != expected_kind {
        return Err(anyhow!(
            r#"error in second word of preamble; expected "{}", got "{}""#,
            expected_kind,
            words[1]
        ));
    }
    let n_args = match words[2].parse::<isize>() {
        Ok(n) if n >= 0 => Some(n as usize),
        _ => return Err(anyhow!("error in preamble: invalid number of arguments")),
    };
    Ok(n_args.unwrap())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ok() {
        let instance = "p af 3\n1 2\n3 3\n";
        let reader = Iccma23Reader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        assert_eq!(3, af.n_arguments());
        assert_eq!(2, af.n_attacks());
        assert!(af
            .iter_attacks()
            .any(|att| att.attacker().id() == 0 && att.attacked().id() == 1));
        assert!(af
            .iter_attacks()
            .any(|att| att.attacker().id() == 2 && att.attacked().id() == 2));
    }

    #[test]
    fn test_ok_missing_last_lf() {
        let instance = "p af 3\n1 2\n3 3";
        let reader = Iccma23Reader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        assert_eq!(3, af.n_arguments());
        assert_eq!(2, af.n_attacks());
        assert!(af
            .iter_attacks()
            .any(|att| att.attacker().id() == 0 && att.attacked().id() == 1));
        assert!(af
            .iter_attacks()
            .any(|att| att.attacker().id() == 2 && att.attacked().id() == 2));
    }

    #[test]
    fn test_ok_empty_lines_at_the_end() {
        let instance = "p af 3\n1 2\n3 3\n\n";
        let reader = Iccma23Reader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        assert_eq!(3, af.n_arguments());
        assert_eq!(2, af.n_attacks());
        assert!(af
            .iter_attacks()
            .any(|att| att.attacker().id() == 0 && att.attacked().id() == 1));
        assert!(af
            .iter_attacks()
            .any(|att| att.attacker().id() == 2 && att.attacked().id() == 2));
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
        let reader = Iccma23Reader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        assert_eq!(3, af.n_arguments());
        assert_eq!(2, af.n_attacks());
        assert!(af
            .iter_attacks()
            .any(|att| att.attacker().id() == 0 && att.attacked().id() == 1));
        assert!(af
            .iter_attacks()
            .any(|att| att.attacker().id() == 2 && att.attacked().id() == 2));
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

    #[test]
    fn test_empty_instance() {
        let instance = "";
        assert!(Iccma23Reader::default()
            .read(&mut instance.as_bytes())
            .is_err());
    }

    #[test]
    fn test_read_arg_from_str() {
        let instance = "p af 1\n";
        let reader = Iccma23Reader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        assert!(reader.read_arg_from_str(&af, "1").is_ok());
        assert!(reader.read_arg_from_str(&af, "2").is_err());
    }

    #[test]
    fn test_arg_in_no_attack() {
        let instance = "p af 1\n";
        let reader = Iccma23Reader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        assert_eq!(1, af.n_arguments());
    }
}
