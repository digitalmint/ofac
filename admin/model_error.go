/*
 * Watchman Admin API
 *
 * Watchman is an HTTP API and Go library to download, parse and offer search functions over numerous trade sanction lists from the United States, European Union governments, agencies, and non profits for complying with regional laws. Also included is a web UI and async webhook notification service to initiate processes on remote systems.
 *
 * API version: v1
 * Generated by: OpenAPI Generator (https://openapi-generator.tech)
 */

package admin

// Error struct for Error
type Error struct {
	// An error message describing the problem intended for humans.
	Error string `json:"error"`
}
