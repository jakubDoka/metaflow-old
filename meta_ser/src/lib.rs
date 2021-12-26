use proc_macro::TokenStream;
use quote::format_ident;
use syn::parse_quote;

#[proc_macro_derive(MetaSer)]
pub fn derive_ser(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);

    let name = &input.ident;

    let mut generics = input.generics.clone();

    for param in generics.type_params_mut() {
        param.bounds.push(parse_quote!(MetaSer));
    }

    let mut type_params = input.generics.clone();
    for param in type_params.type_params_mut() {
        param.bounds.clear();
    }

    let result = match input.data {
        syn::Data::Struct(s) => {
            let is_tuple = s.fields.iter().next().map(|f| f.ident.is_none()).unwrap_or(false);
            if is_tuple {
                let names = (0..s.fields.len()).map(syn::Index::from);
                quote::quote! {
                    impl #generics traits::MetaSer for #name #type_params {
                        fn meta_ser(&self, buffer: &mut Vec<u8>) {
                            #(
                                self.#names.meta_ser(buffer);
                            )*
                        }
                    }
                }
            } else {
                let names = s.fields.iter().map(|f| f.ident.as_ref().unwrap());
                
                quote::quote! {
                    impl #generics traits::MetaSer for #name #type_params {
                        fn meta_ser(&self, buffer: &mut Vec<u8>) {
                            #(
                                self.#names.meta_ser(buffer);
                            )*
                        }
                    }
                }
            }
        },
        syn::Data::Enum(e) => {
            let variants = e.variants.iter().enumerate().map(|(i, v)| {
                let ident = &v.ident;
                let is_tuple = v.fields.iter().next().map(|f| f.ident.is_none()).unwrap_or(false);
                let index = i as u8;

                if is_tuple {
                    let fields = (0..v.fields.len()).map(|i| format_ident!("field{}", i));
                    let fields2 = fields.clone();
                    
                    quote::quote!(
                        #name::#ident( #( #fields ),* ) => {
                            #index.meta_ser(buffer);
                            #(
                                #fields2.meta_ser(buffer);
                            )*
                        }
                    )
                } else {
                    let fields = v.fields.iter().map(|f| f.ident.as_ref().unwrap());
                    let fields2 = fields.clone();
                    
                    quote::quote!(
                        #name::#ident { #( #fields ),* } => {
                            #index.meta_ser(buffer);
                            #(
                                #fields2.meta_ser(buffer);
                            )*
                        }
                    )
                }
            });

            quote::quote! {
                impl #generics traits::MetaSer for #name #type_params {
                    fn meta_ser(&self, buffer: &mut Vec<u8>) {
                        match self {
                            #( #variants )*
                        }
                    }
                }
            }
        },
        syn::Data::Union(_) => panic!("union is not supported"),
    };

    result.into()
}

#[proc_macro_derive(MetaDeSer)]
pub fn derive_de_ser(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);

    let name = &input.ident;

    let mut generics = input.generics.clone();

    for param in generics.type_params_mut() {
        param.bounds.push(parse_quote!(MetaDeSer));
    }

    let mut type_params = input.generics.clone();
    for param in type_params.type_params_mut() {
        param.bounds.clear();
    }

    let result = match input.data {
        syn::Data::Struct(s) => {
            let is_tuple = s.fields.iter().next().map(|f| f.ident.is_none()).unwrap_or(false);
            if is_tuple {
                let names = std::iter::repeat(format_ident!("traits")).take(s.fields.len());

                quote::quote! {
                    impl #generics traits::MetaDeSer for #name #type_params {
                        fn meta_de_ser(progress: &mut usize, buffer: &[u8]) -> Self {
                            Self(#(
                                #names::MetaDeSer::meta_de_ser(progress, buffer),
                            )*)
                        }
                    }
                }
            } else {
                let names = s.fields.iter().map(|f| f.ident.as_ref().unwrap());
                
                quote::quote! {
                    impl #generics traits::MetaDeSer for #name #type_params {
                        fn meta_de_ser(progress: &mut usize, buffer: &[u8]) -> Self {
                            Self {#(
                                #names: traits::MetaDeSer::meta_de_ser(progress, buffer),
                            )*}
                        }
                    }
                }
            }
        },
        syn::Data::Enum(e) => {
            let variants = e.variants.iter().enumerate().map(|(i, v)| {
                let ident = &v.ident;
                let is_tuple = v.fields.iter().next().map(|f| f.ident.is_none()).unwrap_or(false);
                let index = i as u8;

                if is_tuple {
                    let fields = std::iter::repeat(format_ident!("traits")).take(v.fields.len());
                    
                    quote::quote!(
                        #index => {
                            #name::#ident(#(
                                #fields::MetaDeSer::meta_de_ser(progress, buffer),
                            )*)
                        }
                    )
                } else {
                    let fields = v.fields.iter().map(|f| f.ident.as_ref().unwrap());
                    
                    quote::quote!(
                        #index => {
                            #name::#ident {#(
                                #fields: traits::MetaDeSer::meta_de_ser(progress, buffer),
                            )*}
                        }
                    )
                }
            });

            quote::quote! {
                impl #generics traits::MetaDeSer for #name #type_params {
                    fn meta_de_ser(progress: &mut usize, buffer: &[u8]) -> Self {
                        match traits::MetaDeSer::meta_de_ser(progress, buffer) {
                            #( #variants )*
                            _ => panic!("invalid variant"),
                        }
                    }
                }
            }
        },
        syn::Data::Union(_) => panic!("union is not supported"),
    };

    result.into()
}

