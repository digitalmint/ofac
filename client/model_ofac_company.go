/*
 * Watchman API
 *
 * Moov Watchman is an HTTP API and Go library to download, parse and offer search functions over numerous trade sanction lists from the United States, European Union governments, agencies, and non profits for complying with regional laws. Also included is a web UI and async webhook notification service to initiate processes on remote systems.
 *
 * API version: v1
 * Generated by: OpenAPI Generator (https://openapi-generator.tech)
 */

package client

// OfacCompany OFAC Company and metadata
type OfacCompany struct {
	// OFAC Company ID
	ID        string              `json:"ID,omitempty"`
	Sdn       OfacSdn             `json:"sdn,omitempty"`
	Addresses []OfacEntityAddress `json:"addresses,omitempty"`
	Alts      []OfacAlt           `json:"alts,omitempty"`
	Status    OfacCompanyStatus   `json:"status,omitempty"`
}
