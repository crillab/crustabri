use super::{FlatABAInstanceReader, WarningHandler};
use crate::{
    aa::{Argument, ArgumentSet},
    aba::FlatABAFramework,
};
use anyhow::{anyhow, Context, Result};
use std::io::{BufRead, BufReader, Read};

/// A reader for the ICCMA 2025 format dedicated to ABA frameworks.
///
/// This object is used to read a [`FlatABAFramework`] encoded using the ICCMA 2025 input format, as defined on [the competition website](https://argumentationcompetition.org/2025/rules.html).
/// The [`LabelType`](crate::utils::LabelType) of the returned argument frameworks is [`usize`].
///
/// # ICCMA 2025 ABA format
///
/// The following content defines a Flat ABA Framework with eight atoms (given by the indexes `1`, `2`, ...),
/// where 1, 2, and 3 are assumptions; 6, 7, and 8 are their respective contraries; the set of rules is (4 &#8592; 5, 1 ), (5 &#8592;) and (6 &#8592; 2, 3).
///
/// ```text
/// p aba 8
/// # this is a comment
/// a 1
/// a 2
/// a 3
/// c 1 6
/// c 2 7
/// c 3 8
/// r 4 5 1
/// r 5
/// r 6 2 3
/// ```
#[derive(Default)]
pub struct FlatABAReader {
    warning_handlers: Vec<WarningHandler>,
}

impl FlatABAInstanceReader<usize> for FlatABAReader {
    fn read(&self, reader: &mut dyn Read) -> Result<FlatABAFramework<usize>> {
        let br = BufReader::new(reader);
        let mut af = None;
        let mut found_empty_lines = false;
        for (i, line) in br.lines().enumerate() {
            let context = || format!("while reading line with index {}", i);
            let l = line.with_context(context)?;
            if l.starts_with('#') {
                continue;
            }
            if l.trim().is_empty() {
                found_empty_lines = true;
                continue;
            }
            if found_empty_lines {
                return Err(anyhow!("got content after an empty line")).with_context(context);
            }
            let words = l.split_whitespace().collect::<Vec<&str>>();
            if af.is_none() {
                let n_args = read_preamble(&words, "aba").with_context(context)?;
                let argument_set =
                    ArgumentSet::new_with_labels((1..=n_args).collect::<Vec<usize>>().as_slice());
                af = Some(FlatABAFramework::new_with_argument_set(argument_set));
                continue;
            }
            let n_args = af.as_ref().unwrap().argument_set().len();
            let read_arg = |word: &str| match word.parse::<isize>() {
                Ok(n) if n >= 1 && (n as usize) <= n_args => Ok(n as usize),
                _ => Err(anyhow!(r#"error: invalid argument index {word}"#,)),
            };
            let expect_n_words = |first, expected| {
                if expected != words.len() {
                    Err(anyhow!(r#"wrong number of words for a "{first}" line; expected {expected}, got {}"#, words.len())).with_context(context)
                } else {
                    Ok(())
                }
            };
            match words[0] {
                "a" => {
                    expect_n_words("a", 2)?;
                    let assumption = read_arg(words[1])?;
                    af.as_mut()
                        .unwrap()
                        .set_as_assumption_by_id(assumption - 1)?;
                }
                "c" => {
                    expect_n_words("c", 3)?;
                    let assumption = read_arg(words[1])?;
                    let contrary = read_arg(words[2])?;
                    af.as_mut()
                        .unwrap()
                        .set_as_contrary_by_ids(contrary - 1, assumption - 1)?;
                }
                "r" => {
                    if words.len() == 1 {
                        return Err(anyhow!(
                            r#"wrong number of words for a "r" line; expected at least 2, got {}"#,
                            words.len()
                        ))
                        .with_context(context);
                    }
                    let head_id = read_arg(words[1])? - 1;
                    let tail_id_vec = words
                        .iter()
                        .skip(2)
                        .map(|w| read_arg(w).map(|label| label - 1))
                        .collect::<Result<Vec<_>>>()?;
                    af.as_mut().unwrap().add_rule_by_ids(head_id, tail_id_vec)?;
                }
                _ => {
                    return Err(anyhow!(r#"unexpected first word "{}""#, words[0]))
                        .with_context(context)
                }
            }
        }
        if af.is_none() {
            return Err(anyhow!("missing preamble"));
        }
        Ok(af.unwrap())
    }

    fn read_arg_from_str<'a>(
        &self,
        af: &'a FlatABAFramework<usize>,
        arg: &str,
    ) -> anyhow::Result<&'a Argument<usize>> {
        match arg.parse::<usize>() {
            Ok(n) if n > 0 && n <= af.argument_set().len() => {
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
        let str_af = r#"p aba 8
        a 1
        a 2
        a 3
        c 1 6
        c 2 7
        c 3 8
        r 4 5 1
        r 5
        r 6 2 3
        "#;
        let reader = FlatABAReader::default();
        let af = reader.read(&mut str_af.as_bytes()).unwrap();
        assert_eq!(
            vec![1, 2, 3],
            af.iter_assumptions()
                .map(|a| *a.label())
                .collect::<Vec<_>>()
        );
        assert_eq!(
            vec![(6, vec![1]), (7, vec![2]), (8, vec![3])],
            af.iter_contraries()
                .map(|(c, a)| (*c.label(), a.map(|l| *l.label()).collect::<Vec<_>>()))
                .collect::<Vec<_>>()
        );
        assert_eq!(
            vec![
                (1, vec![]),
                (2, vec![]),
                (3, vec![]),
                (4, vec![vec![5, 1]]),
                (5, vec![vec![]]),
                (6, vec![vec![2, 3]]),
                (7, vec![]),
                (8, vec![]),
            ],
            af.iter_rules()
                .map(|(head, tails)| (
                    *head.label(),
                    tails
                        .iter()
                        .map(|t| t.iter().map(|a| *a.label()).collect())
                        .collect()
                ))
                .collect::<Vec<_>>()
        );
    }
}
