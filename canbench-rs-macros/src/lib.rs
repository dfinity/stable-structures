use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, ItemFn};

#[proc_macro_attribute]
pub fn bench(_attr: TokenStream, item: TokenStream) -> TokenStream {
    // Parse the input as a function
    let input = parse_macro_input!(item as ItemFn);

    // Extract function name, inputs, and output
    let func_name = &input.sig.ident;
    let inputs = &input.sig.inputs;
    let output = &input.sig.output;

    // Check that there are no function arguments
    if !inputs.is_empty() {
        return syn::Error::new_spanned(inputs, "Benchmark should not take any arguments")
            .to_compile_error()
            .into();
    }

    // Check that the return type is BenchResult
    match output {
        syn::ReturnType::Default => {
            return syn::Error::new_spanned(output, "Benchmark should return BenchResult")
                .to_compile_error()
                .into();
        }
        syn::ReturnType::Type(_, ty) => {
            if quote!(#ty).to_string() != "BenchResult" {
                return syn::Error::new_spanned(ty, "Benchmark should return BenchResult")
                    .to_compile_error()
                    .into();
            }
        }
    }

    // Prefix the benchmark name with "__canbench__".
    // This is to inform that the `canbench` binary that this query is a benchmark
    // that it should run.
    let renamed_func_name =
        syn::Ident::new(&format!("__canbench__{}", func_name), func_name.span());
    let expanded = quote! {
        #input

        #[ic_cdk::query]
        #[allow(non_snake_case)]
        fn #renamed_func_name() -> BenchResult {
            #func_name()
        }
    };

    TokenStream::from(expanded)
}
