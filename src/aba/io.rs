use super::Language;
use crate::{aba::ABAFramework, io::iccma23_reader};
use anyhow::{anyhow, Context, Result};
use std::{
    fmt::Display,
    io::{BufRead, BufReader, Read, Write},
};

/// A reader for the ICCMA 2023 ABA format.
#[derive(Default)]
pub struct Iccma23ABAReader;

impl Iccma23ABAReader {
    /// Reads an Assumption-based Argumentation framework.
    pub fn read(&mut self, reader: &mut dyn Read) -> Result<ABAFramework<usize>> {
        let br = BufReader::new(reader);
        let mut aba = None;
        let mut assumption_with_no_contrary = None;
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
            if aba.is_none() {
                let n_args = iccma23_reader::read_preamble(&words, "aba").with_context(context)?;
                let language =
                    Language::new_with_labels((1..=n_args).collect::<Vec<usize>>().as_slice());
                aba = Some(ABAFramework::new_with_language(language));
                assumption_with_no_contrary = Some(vec![false; 1 + n_args]);
                continue;
            }

            let check_line_len = |line_type, n| {
                if n != words.len() {
                    Err(anyhow!(
                        r#"error in {} line; expected {} words, got {}"#,
                        line_type,
                        n,
                        words.len()
                    ))
                } else {
                    Ok(())
                }
            };
            let read_atom_index = |word: &str| match word.parse::<isize>() {
                Ok(n) if n >= 1 && (n as usize) <= aba.as_ref().unwrap().language().len() => {
                    Ok(n as usize)
                }
                _ => Err(anyhow!("invalid atom index")),
            };
            match words[0] {
                "a" => {
                    check_line_len("assumption", 2).with_context(context)?;
                    let atom_index = read_atom_index(words[1]).with_context(context)?;
                    assumption_with_no_contrary.as_mut().unwrap()[atom_index] = true;
                }
                "c" => {
                    check_line_len("contrary", 3).with_context(context)?;
                    let atom_index = read_atom_index(words[1]).with_context(context)?;
                    let contrary_index = read_atom_index(words[2]).with_context(context)?;
                    if !assumption_with_no_contrary.as_mut().unwrap()[atom_index] {
                        return Err(anyhow!(
                            "cannot define a contrary for non-assumption atom {}",
                            atom_index
                        ));
                    }
                    assumption_with_no_contrary.as_mut().unwrap()[atom_index] = false;
                    aba.as_mut()
                        .unwrap()
                        .new_assumption(&atom_index, &contrary_index)
                        .with_context(context)?;
                }
                "r" => {
                    if words.len() == 1 {
                        return Err(anyhow!(
                            r#"error in rule line; expected at least 2 words, got {}"#,
                            words.len()
                        ));
                    }
                    let head_index = read_atom_index(words[1]).with_context(context)?;
                    let body_indices = words
                        .iter()
                        .skip(2)
                        .map(|w| read_atom_index(w))
                        .collect::<Result<Vec<usize>>>()
                        .with_context(context)?;
                    let body_indices_refs = body_indices.iter().collect::<Vec<&usize>>();
                    aba.as_mut()
                        .unwrap()
                        .new_rule(&head_index, &body_indices_refs)
                        .with_context(context)?;
                }
                _ => return Err(anyhow!("unknown line type")),
            }
        }
        if aba.is_none() {
            return Err(anyhow!("missing preamble"));
        }
        if let Some(p) = assumption_with_no_contrary
            .as_ref()
            .unwrap()
            .iter()
            .position(|a| *a)
        {
            return Err(anyhow!("undefined contrary for assumption {}", p))
                .context("while finalizing the result")?;
        }
        Ok(aba.unwrap())
    }
}

/// A structure used to write answers for ICCMA'23 ABA tracks.
#[derive(Default)]
pub struct Iccma23ABAWriter;

impl Iccma23ABAWriter {
    /// Writes the text associated with the fact the problem has no extension.
    pub fn write_no_extension(&self, writer: &mut dyn Write) -> Result<()> {
        let context = "while writing problem has no extension";
        writeln!(writer, "NO").context(context)?;
        writer.flush().context(context)
    }

    /// Writes a single extension.
    pub fn write_single_extension<I, T>(&self, writer: &mut dyn Write, extension: I) -> Result<()>
    where
        I: IntoIterator<Item = T>,
        T: Display,
    {
        let context = "while writing an extension";
        write!(writer, "w").context(context)?;
        extension
            .into_iter()
            .try_for_each(|t| write!(writer, " {}", t).context(context))?;
        writeln!(writer).context(context)?;
        writer.flush().context(context)
    }

    /// Writes an acceptance status.
    pub fn write_acceptance_status(
        &self,
        writer: &mut dyn Write,
        acceptance_status: bool,
    ) -> Result<()> {
        let context = "while writing an acceptance_status";
        writeln!(writer, "{}", if acceptance_status { "YES" } else { "NO" }).context(context)?;
        writer.flush().context(context)
    }
}
